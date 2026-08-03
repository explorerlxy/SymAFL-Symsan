#include "pcbt.hpp"

namespace pcbt {

namespace {
const char *pkind_name(PKind kind) {
  switch (kind) {
    case PKind::Opaque: return "opaque";
    case PKind::Read: return "read";
    case PKind::Const: return "const";
    case PKind::Add: return "add";
    case PKind::Sub: return "sub";
    case PKind::Mul: return "mul";
    case PKind::UDiv: return "udiv";
    case PKind::SDiv: return "sdiv";
    case PKind::URem: return "urem";
    case PKind::SRem: return "srem";
    case PKind::Neg: return "neg";
    case PKind::Not: return "not";
    case PKind::And: return "and";
    case PKind::Or: return "or";
    case PKind::Xor: return "xor";
    case PKind::Shl: return "shl";
    case PKind::LShr: return "lshr";
    case PKind::AShr: return "ashr";
    case PKind::Equal: return "eq";
    case PKind::Distinct: return "ne";
    case PKind::Ult: return "ult";
    case PKind::Ule: return "ule";
    case PKind::Ugt: return "ugt";
    case PKind::Uge: return "uge";
    case PKind::Slt: return "slt";
    case PKind::Sle: return "sle";
    case PKind::Sgt: return "sgt";
    case PKind::Sge: return "sge";
    case PKind::ZExt: return "zext";
    case PKind::SExt: return "sext";
    case PKind::Extract: return "extract";
    case PKind::Concat: return "concat";
    case PKind::Memcmp: return "memcmp";
    case PKind::Len: return "len";
    case PKind::EofRead: return "eofread";
    case PKind::Count: return "count";
    case PKind::CountNeg1: return "countneg1";
    case PKind::CountElems: return "countelems";
  }
  return "?";
}
}  // namespace

Tree::Tree() : nodes_(kRoot + 1) {
  pred_arena_.nodes.reserve(4096);
}

void Tree::DebugPredicate(NodeRef ref, const uint8_t *input,
                          uint32_t len) const {
  if (ref == kUnexplored || ref == kTerminal || ref == kRoot) return;
  const Node &n = node(ref);
  fprintf(stderr, "[pcbt-dbg] node=%u cid=%u depth=%u opaque=%d\n",
          ref, n.cid, n.depth, n.pred.opaque ? 1 : 0);
  if (n.pred.opaque) return;
  fprintf(stderr, "[pcbt-dbg] reads:");
  for (const auto &r : n.pred.reads) {
    fprintf(stderr, " %u+%u=[", r.first, r.second);
    for (uint32_t k = 0; k < r.second && r.first + k < len; k++)
      fprintf(stderr, "%02x", input[r.first + k]);
    fprintf(stderr, "]");
  }
  fprintf(stderr, "\n");
  std::vector<uint32_t> stack;
  if (n.pred.root < pred_arena_.nodes.size())
    stack.push_back(n.pred.root);
  while (!stack.empty()) {
    uint32_t idx = stack.back();
    stack.pop_back();
    if (idx >= pred_arena_.nodes.size()) continue;
    const PNode &p = pred_arena_.nodes[idx];
    fprintf(stderr, "[pcbt-dbg]   %u %s bits=%u value=%llu a=%u b=%u\n",
            idx, pkind_name(p.kind), p.bits, (unsigned long long)p.value,
            p.a, p.b);
    if (p.a != UINT32_MAX) stack.push_back(p.a);
    if (p.b != UINT32_MAX) stack.push_back(p.b);
  }
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
  for (const Event &ev : events) num_events += ev.count;

  NodeRef parent = kRoot;
  uint8_t dir = 0;
  uint64_t trace_depth = 0;
  size_t i = 0;
  uint16_t k = 0;  // consumed logical events inside the current frame
  // Prefix match: advance along existing edges one logical event at a time.
  // A fold frame contributes `count` logical events with the same cid/result.
  while (i < events.size()) {
    const Event &ev = events[i];
    NodeRef next = node(parent).child[dir];
    if (next == kUnexplored) break;
    if (next == kTerminal || node(next).cid != ev.cid) {
      num_conflicts += 1;
      return 0;
    }
    parent = next;
    dir = ev.result ? 1 : 0;
    trace_depth += 1;
    k += 1;
    if (k == ev.count) {
      k = 0;
      i += 1;
    }
  }

  if (i == events.size() && k == 0) {
    if (node(parent).child[dir] == kUnexplored) {
      node(parent).child[dir] = kTerminal;
    }
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  for (; i < events.size(); ++i) {
    const Event &ev = events[i];
    std::vector<Predicate> preds;
    if (ev.count > 1) {
      // `k` is nonzero when the tree already covered this frame's prefix;
      // expand only the remaining logical events.
      conv.expand_fold(ev.label, ev.count, k, &preds);
    } else {
      preds.push_back(conv.conv(ev.label));
    }
    k = 0;
    for (const Predicate &pred : preds) {
      Node new_node;
      new_node.cid = ev.cid;
      new_node.depth = parent == kRoot ? 1 : node(parent).depth + 1;
      new_node.pred = pred;
      if (pred.opaque) {
        num_opaque += 1;
        opaque_by_error[static_cast<size_t>(pred.error)] += 1;
        if (pred.error_op) opaque_by_op[pred.error_op] += 1;
      }
      NodeRef next = append(std::move(new_node));
      if (next == kUnexplored) return created;
      node(parent).child[dir] = next;
      parent = next;
      dir = ev.result ? 1 : 0;
      created += 1;
      trace_depth += 1;
    }
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
  for (const Event &ev : events) num_events += ev.count;

  if (events.empty()) {
    node(parent).child[direction] = kTerminal;
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  uint8_t dir = direction;
  NodeRef cur = parent;
  for (const Event &event : events) {
    std::vector<Predicate> preds;
    if (event.count > 1) {
      conv.expand_fold(event.label, event.count, 0, &preds);
    } else {
      preds.push_back(conv.conv(event.label));
    }
    for (const Predicate &pred : preds) {
      Node new_node;
      new_node.cid = event.cid;
      new_node.depth = node(cur).depth + 1;
      new_node.pred = pred;
      if (pred.opaque) {
        num_opaque += 1;
        opaque_by_error[static_cast<size_t>(pred.error)] += 1;
        if (pred.error_op) opaque_by_op[pred.error_op] += 1;
      }
      NodeRef next = append(std::move(new_node));
      if (next == kUnexplored) return created;
      node(cur).child[dir] = next;
      cur = next;
      dir = event.result ? 1 : 0;
      created += 1;
    }
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
  size_t logic = 0;  // verified logical events (fold frames expand)
  size_t trace_total = 0;
  for (const Event &ev : events) trace_total += ev.count;
  size_t i = 0;
  // Validate one logical event against the tree. Returns false when the
  // replay must stop (r already describes the outcome).
  auto step = [&](const Event &ev) -> bool {
    logic += 1;
    if (ev.result > 1) {
      r.error = ReplayError::InvalidEventResult;
      r.event_index = i;
      return false;
    }
    const Node &current = node(cur);
    // CID check
    if (current.cid != ev.cid) {
      if (debug_) DebugPredicate(cur, input, len);
      r.error = ReplayError::CidMismatch;
      r.event_index = i;
      r.expected_cid = current.cid;
      r.observed_cid = ev.cid;
      return false;
    }
    // Constraint events (tainted GEP index / indcall target == concrete)
    // record result always 1: the constraint held for the traced run. The
    // stored predicate is screening semantics (evaluates 0 for candidates
    // whose index differs), so direction validation would be a false
    // positive. Follow the recorded direction; the next event's CID check
    // still guards the path.
    if (ev.constraint) {
      NodeRef next = current.child[ev.result ? 1 : 0];
      if (next == kTerminal) {
        if (logic < trace_total) {
          r.error = ReplayError::AfterTerminal;
          r.event_index = i;
          r.verified_events = logic;
          return false;
        }
        r.event_index = i;
        r.verified_events = logic;
        r.reached_terminal = true;
        return false;
      }
      if (next == kUnexplored) {
        r.event_index = i;
        r.verified_events = logic;
        r.reached_frontier = true;
        r.frontier_node = cur;
        r.frontier_dir = ev.result ? 1 : 0;
        r.suffix_begin = logic;
        return false;
      }
      cur = next;
      return true;
    }
    // Evaluate predicate
    if (current.pred.opaque) {
      r.event_index = i;
      r.verified_events = logic - 1;  // events before this opaque one
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = ev.result;
      r.opaque_admission = true;
      return false;
    }
    uint64_t v = 0;
    if (!eval_predicate(pred_arena_, current.pred, input, len, &v, &eval)) {
      r.event_index = i;
      r.verified_events = logic - 1;
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = ev.result;
      r.eval_failure = true;
      return false;
    }
    uint8_t dir = v ? 1 : 0;
    r.direction_checked = true;
    if (dir != ev.result) {
      if (debug_) DebugPredicate(cur, input, len);
      r.error = ReplayError::DirectionMismatch;
      r.event_index = i;
      r.expected_cid = current.cid;
      r.observed_cid = ev.cid;
      r.evaluated_dir = dir;
      r.observed_dir = ev.result;
      return false;
    }
    NodeRef next = current.child[dir];
    if (next == kTerminal) {
      if (logic < trace_total) {
        // More events follow, but trace already consumed
        r.error = ReplayError::AfterTerminal;
        r.event_index = i;
        r.verified_events = logic;
        return false;
      }
      // Last event ends exactly at a terminal edge: consistent.
      r.event_index = i;
      r.verified_events = logic;
      r.reached_terminal = true;
      return false;
    }
    if (next == kUnexplored) {
      r.event_index = i;
      r.verified_events = logic;  // this event passed all checks
      r.reached_frontier = true;
      r.frontier_node = cur;
      r.frontier_dir = dir;
      r.suffix_begin = logic;
      return false;
    }
    cur = next;
    return true;
  };

  bool stopped = false;
  for (; i < events.size(); ++i) {
    const Event &ev = events[i];
    bool cont = true;
    for (uint16_t k = 0; k < ev.count && cont; ++k) cont = step(ev);
    if (!cont) {
      stopped = true;
      break;
    }
  }
  if (!stopped) {
    // All events consumed without hitting terminal or frontier: the tree
    // expects more conditions.  This can happen after the last event if
    // cur.child[dir] points to another node (not kTerminal/Unexplored).
    r.verified_events = logic;
    r.event_index = i;
    r.error = ReplayError::TruncatedTrace;
    if (debug_) DebugPredicate(cur, input, len);
  }
  return r;
}

}  // namespace pcbt
