#include "pcbt.hpp"

namespace pcbt {

Tree::Tree() : nodes_(kRoot + 1) {
  pred_arena_.nodes.reserve(4096);
}

NodeRef Tree::append(Node &&new_node) {
  if (nodes_.size() == UINT32_MAX) return kUnexplored;
  nodes_.push_back(std::move(new_node));
  return (NodeRef)nodes_.size() - 1;
}

uint32_t Tree::InsertTrace(const std::vector<Event> &events,
                           const dfsan_label_info *table,
                           size_t table_labels) {
  if (events.empty()) return 0;
  num_traces += 1;
  num_events += events.size();

  NodeRef parent = kRoot;
  uint8_t dir = 0;
  uint64_t trace_depth = 0;
  size_t i = 0;
  for (; i < events.size(); ++i) {
    NodeRef next = node(parent).child[dir];
    if (next == kUnexplored) break;
    if (next == kTerminal || node(next).cid != events[i].cid) {
      num_conflicts += 1;
      return 0;
    }
    parent = next;
    dir = events[i].result ? 1 : 0;
    trace_depth += 1;
  }

  if (i == events.size()) {
    if (node(parent).child[dir] == kUnexplored) {
      node(parent).child[dir] = kTerminal;
    }
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  for (; i < events.size(); ++i) {
    Node new_node;
    new_node.cid = events[i].cid;
    new_node.depth = parent == kRoot ? 1 : node(parent).depth + 1;
    new_node.pred = conv.conv(events[i].label);
    new_node.min_len = pred_read_extent(new_node.pred);
    if (new_node.pred.opaque) {
      num_opaque += 1;
      opaque_by_error[static_cast<size_t>(new_node.pred.error)] += 1;
      if (new_node.pred.error_op) opaque_by_op[new_node.pred.error_op] += 1;
    }
    NodeRef next = append(std::move(new_node));
    if (next == kUnexplored) return created;
    node(parent).child[dir] = next;
    parent = next;
    dir = events[i].result ? 1 : 0;
    created += 1;
    trace_depth += 1;
  }

  node(parent).child[dir] = kTerminal;
  num_nodes += created;
  if (trace_depth > max_depth) max_depth = trace_depth;
  return created;
}

uint32_t Tree::InsertSuffix(NodeRef parent, uint8_t direction,
                            const std::vector<Event> &events,
                            const dfsan_label_info *table,
                            size_t table_labels) {
  if (parent < kRoot || parent >= nodes_.size() || direction > 1 ||
      node(parent).child[direction] != kUnexplored) {
    return 0;
  }
  num_traces += 1;
  num_events += events.size();

  if (events.empty()) {
    node(parent).child[direction] = kTerminal;
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  uint8_t dir = direction;
  NodeRef cur = parent;
  for (const Event &event : events) {
    Node new_node;
    new_node.cid = event.cid;
    new_node.depth = node(cur).depth + 1;
    new_node.pred = conv.conv(event.label);
    new_node.min_len = pred_read_extent(new_node.pred);
    if (new_node.pred.opaque) {
      num_opaque += 1;
      opaque_by_error[static_cast<size_t>(new_node.pred.error)] += 1;
      if (new_node.pred.error_op) opaque_by_op[new_node.pred.error_op] += 1;
    }
    NodeRef next = append(std::move(new_node));
    if (next == kUnexplored) return created;
    node(cur).child[dir] = next;
    cur = next;
    dir = event.result ? 1 : 0;
    created += 1;
  }

  node(cur).child[dir] = kTerminal;
  num_nodes += created;
  if (node(cur).depth > max_depth) max_depth = node(cur).depth;
  return created;
}

bool Tree::CheckInput(const uint8_t *input, uint32_t len, NodeRef *out_node,
                      uint8_t *out_dir, uint8_t rlimit) {
  NodeRef cur = node(kRoot).child[0];
  if (cur == kUnexplored) {
    *out_node = kUnexplored;
    *out_dir = 0;
    check_admit_empty += 1;
    return true;
  }

  EvalContext eval;
  eval.Reset();
  while (true) {
    const Node &current = node(cur);
    // The input length is a first-class constraint: a candidate shorter than
    // this node's predicate reads is in a different (shallower) subtree and
    // cannot be screened through it. Admit conservatively instead of
    // evaluating an out-of-range read.
    if (current.min_len > len) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_too_short += 1;
      return true;
    }
    if (current.pred.opaque) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_opaque += 1;
      return true;
    }
    uint64_t v = 0;
    if (!eval_predicate(pred_arena_, current.pred, input, len, &v, &eval)) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_eval_failure += 1;
      return true;
    }
    uint8_t dir = v ? 1 : 0;
    NodeRef next = current.child[dir];
    if (next == kTerminal) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_veto_terminal += 1;
      return false;
    }
    if (next == kUnexplored) {
      *out_node = cur;
      *out_dir = dir;
      if (current.rCnt[dir] < rlimit) {
        check_admit_frontier += 1;
        return true;
      }
      check_veto_rlimit += 1;
      return false;
    }
    cur = next;
  }
}

bool Tree::IsSaturated(uint8_t rlimit) const {
  NodeRef entry = node(kRoot).child[0];
  return entry != kUnexplored && IsSaturated(entry, rlimit);
}

bool Tree::IsSaturated(NodeRef ref, uint8_t rlimit) const {
  const Node &current = node(ref);
  if (current.pred.opaque) return false;
  for (uint8_t direction = 0; direction != 2; ++direction) {
    NodeRef next = current.child[direction];
    if (next == kTerminal) continue;
    if (next == kUnexplored) {
      if (current.rCnt[direction] < rlimit) return false;
      continue;
    }
    if (!IsSaturated(next, rlimit)) return false;
  }
  return true;
}

Tree::ReplayReport Tree::ReplayFullTrace(
    const std::vector<Event> &events, const uint8_t *input,
    uint32_t len) const {
  ReplayReport r;

  NodeRef cur = node(kRoot).child[0];
  if (cur == kUnexplored) {
    r.tree_empty = true;
    return r;
  }

  EvalContext eval;
  eval.Reset();
  size_t i = 0;
  for (; i < events.size(); ++i) {
    const Event &ev = events[i];
    if (ev.result > 1) {
      r.error = ReplayError::InvalidEventResult;
      r.event_index = i;
      return r;
    }
    const Node &current = node(cur);
    // CID check
    if (current.cid != ev.cid) {
      r.error = ReplayError::CidMismatch;
      r.event_index = i;
      r.expected_cid = current.cid;
      r.observed_cid = ev.cid;
      return r;
    }
    // Evaluate predicate
    if (current.pred.opaque) {
      r.event_index = i;
      r.verified_events = i;  // events before this opaque one are verified
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = ev.result;
      r.opaque_admission = true;
      return r;
    }
    uint64_t v = 0;
    if (!eval_predicate(pred_arena_, current.pred, input, len, &v, &eval)) {
      r.event_index = i;
      r.verified_events = i;
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = ev.result;
      r.eval_failure = true;
      return r;
    }
    uint8_t dir = v ? 1 : 0;
    r.direction_checked = true;
    if (dir != ev.result) {
      r.error = ReplayError::DirectionMismatch;
      r.event_index = i;
      r.expected_cid = current.cid;
      r.observed_cid = ev.cid;
      r.evaluated_dir = dir;
      r.observed_dir = ev.result;
      return r;
    }
    NodeRef next = current.child[dir];
    if (next == kTerminal) {
      if (i + 1 < events.size()) {
        // More events follow, but trace already consumed
        r.error = ReplayError::AfterTerminal;
        r.event_index = i + 1;
        r.verified_events = i + 1;
        return r;
      }
      // Last event ends exactly at a terminal edge: consistent.
      r.event_index = i;
      r.verified_events = i + 1;
      r.reached_terminal = true;
      return r;
    }
    if (next == kUnexplored) {
      r.event_index = i;
      r.verified_events = i + 1;  // this event passed all checks
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = dir;
      r.suffix_begin = i + 1;
      return r;
    }
    cur = next;
  }

  // All events consumed without hitting terminal or frontier: the tree
  // expects more conditions.  This can happen after the last event if
  // cur.child[dir] points to another node (not kTerminal/Unexplored).
  r.verified_events = i;
  r.event_index = i;
  r.error = ReplayError::TruncatedTrace;
  return r;
}

}  // namespace pcbt
