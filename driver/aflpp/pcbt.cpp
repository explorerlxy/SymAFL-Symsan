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

// Does the predicate's DAG contain a length/count-family leaf?
// Length-derived decisions are path-dependent in label presence (a trace
// whose length counter was never symbolically updated contributes no event,
// candidates on other paths do), so terminal vetoes at such nodes are not
// trustworthy. See Node::len_related.
//
// The visited set is a generation-stamped array of arena size instead of a
// freshly allocated per-call vector: this runs once per new tree node, and a
// per-node `vector<uint8_t> visited(arena.nodes.size(), 0)` zero-fills the
// whole arena per node (the profiled 74% memset in InsertSuffix).
static bool pred_has_len_kind(const PredArena &arena, const Predicate &pred) {
  if (pred.opaque || pred.root >= arena.nodes.size()) return false;
  static thread_local std::vector<uint32_t> visited;
  static thread_local uint32_t generation = 0;
  if (visited.size() < arena.nodes.size()) {
    visited.resize(arena.nodes.size(), 0);
  }
  if (++generation == 0) {  // wrap: stale stamps would read as visited
    std::fill(visited.begin(), visited.end(), 0);
    generation = 1;
  }
  std::vector<uint32_t> stack = {pred.root};
  while (!stack.empty()) {
    uint32_t idx = stack.back();
    stack.pop_back();
    if (idx >= arena.nodes.size() || visited[idx] == generation) continue;
    visited[idx] = generation;
    const PNode &p = arena.nodes[idx];
    switch (p.kind) {
      case PKind::Len:
      case PKind::EofRead:
      case PKind::Count:
      case PKind::CountNeg1:
      case PKind::CountElems:
        return true;
      default:
        break;
    }
    if (p.a != UINT32_MAX) stack.push_back(p.a);
    if (p.b != UINT32_MAX) stack.push_back(p.b);
  }
  return false;
}

// skipCnt assignment for a new node: constraint nodes share the parent's
// skipCnt (the candidate re-emits its own constraint event at the same
// stream position), ordinary nodes advance by one stream position — plus
// one extra when the parent is a constraint, because the constraint event
// itself also occupies a stream position.
static inline uint32_t child_skip_cnt(const Node &parent, bool constraint) {
  if (constraint) return parent.skipCnt;
  return parent.skipCnt + (parent.constraint ? 2 : 1);
}

uint32_t Tree::InsertTrace(const std::vector<Event> &events,
                           const dfsan_label_info *table,
                           size_t table_labels,
                           const uint8_t *input, uint32_t len) {
  if (events.empty()) return 0;
  num_traces += 1;
  for (const Event &ev : events) num_events += ev.count;

  NodeRef parent = kRoot;
  uint8_t dir = 0;
  uint64_t trace_depth = 0;
  size_t i = 0;
  uint16_t k = 0;  // consumed logical events inside the current frame
  EvalContext eval;
  eval.Reset();
  // Prefix match: walk the tree by evaluating each visited node's predicate
  // against the candidate input (symmetric with CheckInput). One stream
  // event is consumed per non-constraint node, and additionally when the
  // walk steps from a constraint node onto a non-constraint child (the
  // candidate's replacement constraint event shares its stream position
  // with the value-chain, so stepping INTO a constraint consumes nothing).
  NodeRef cur = node(kRoot).child[0];
  while (i < events.size() && cur != kUnexplored && cur != kTerminal) {
    const Event &ev = events[i];
    const Node &cn = node(cur);
    uint64_t v = 0;
    uint8_t edir;
    if (cn.pred.opaque || input == nullptr ||
        !eval_predicate(pred_arena_, cn.pred, input, len, &v, &eval)) {
      edir = ev.result ? 1 : 0;  // follow the recorded direction
    } else {
      edir = v ? 1 : 0;
    }
    trace_depth += 1;
    parent = cur;
    dir = edir;
    NodeRef nxt = node(parent).child[dir];
    if (!cn.constraint ||
        (nxt != kUnexplored && nxt != kTerminal && !node(nxt).constraint)) {
      k += 1;
      if (k == ev.count) {
        k = 0;
        i += 1;
      }
    }
    cur = nxt;
  }
  // `parent`/`dir` address the edge where the walk stopped; `i`/`k` index
  // the first unconsumed stream event.
  if (cur == kTerminal && i < events.size()) {
    // The evaluated path reaches an explored-terminal edge while the trace
    // still has events: prefix drift (or a suffix-truncated earlier
    // insertion). Discard; never insert.
    num_conflicts += 1;
    return 0;
  }

  if (i == events.size() && k == 0) {
    if (node(parent).child[dir] == kUnexplored) {
      // A trace ending right after a constraint event has only observed the
      // pinned value; the tail edge must stay unexplored so unseen values
      // reach a frontier.
      if (!node(parent).constraint)
        node(parent).child[dir] = kTerminal;
    }
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  for (; i < events.size(); ++i) {
    const Event &ev = events[i];
    // Constraint re-emission: a candidate that pins the same value as the
    // parent constraint node re-emits the parent's own event at the same
    // stream position (multi-successor single-decision semantics: every
    // candidate contributes exactly one event at the decision point). It is
    // already modeled by the parent node, so skip it — the parent's dir-1
    // subtree then starts at the candidate's first post-decision event.
    // (A different pinned value produces a different label and is inserted
    // as the value-fork chain instead.)
    if (ev.constraint && node(parent).constraint &&
        ev.cid == node(parent).cid && ev.label == node(parent).label) {
      continue;
    }
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
      new_node.label = ev.label;
      new_node.depth = parent == kRoot ? 1 : node(parent).depth + 1;
      new_node.skipCnt = parent == kRoot
          ? (ev.constraint ? 0u : 1u)
          : child_skip_cnt(node(parent), ev.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = ev.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
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

  // A trace ending right after a constraint event has only observed the
  // pinned value; the tail edge stays unexplored.
  if (!events.back().constraint)
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
    // Empty suffix on a constraint edge: the run only confirmed that the
    // pinned value produces no further symbolic decisions. Other values are
    // unobserved, so the edge must stay unexplored.
    if (!node(parent).constraint)
      node(parent).child[direction] = kTerminal;
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  uint8_t dir = direction;
  NodeRef cur = parent;
  for (const Event &event : events) {
    // Constraint re-emission filter (symmetric with InsertTrace): the
    // suffix capture skips `parent.skipCnt` events, so a candidate admitted
    // on the parent's dir-1 (pinned-value) edge re-emits the parent's own
    // event as the first captured event. It is already modeled; skip it so
    // the dir-1 subtree starts at the candidate's first post-decision
    // event. A candidate pinning a different value (admitted on dir-0)
    // re-emits its own different-label event, which is inserted as the
    // value-fork chain. When every event is filtered (only the re-emission
    // was captured), the edge stays unexplored — the run only confirmed the
    // pinned value produces no further decisions.
    if (event.constraint && node(cur).constraint &&
        event.cid == node(cur).cid && event.label == node(cur).label) {
      continue;
    }
    std::vector<Predicate> preds;
    if (event.count > 1) {
      conv.expand_fold(event.label, event.count, 0, &preds);
    } else {
      preds.push_back(conv.conv(event.label));
    }
    for (const Predicate &pred : preds) {
      Node new_node;
      new_node.cid = event.cid;
      new_node.label = event.label;
      new_node.depth = node(cur).depth + 1;
      new_node.skipCnt = child_skip_cnt(node(cur), event.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = event.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
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

  // A suffix ending right after a constraint event has only observed the
  // pinned value; the tail edge stays unexplored.
  if (!events.back().constraint)
    node(cur).child[dir] = kTerminal;
  num_nodes += created;
  if (node(cur).depth > max_depth) max_depth = node(cur).depth;
  return created;
}

bool Tree::CheckInput(const uint8_t *input, uint32_t len, NodeRef *out_node,
                      uint8_t *out_dir, uint8_t rlimit,
                      uint32_t *out_veto_depth, NodeRef *out_veto_node,
                      uint8_t *out_veto_dir, uint8_t *out_veto_kind) {
  NodeRef cur = node(kRoot).child[0];
  if (cur == kUnexplored) {
    *out_node = kUnexplored;
    *out_dir = 0;
    check_admit_empty += 1;
    return true;
  }

  // The context persists across candidates (vectors amortized instead of
  // re-filled to the arena size per check; the per-check zero-fill of
  // values_/stamps_ was the profiled check cost at large arena sizes).
  EvalContext &eval = check_eval_;
  eval.Reset();
  while (true) {
    const Node &current = node(cur);
    if (current.pred.opaque) {
      // Opaque nodes from return-value comparisons (compile-time
      // instrumentation of ret != CONST where DFSan constant-folded the call
      // result to shadow 0) mark decisions that exist but cannot be
      // evaluated for candidates. Near the root they must not collapse
      // screening (an admit would let every candidate through): follow the
      // stored direction there - routing is then identical to the decision
      // being absent. Deeper opaque nodes (e.g. index_hash.c:189 at depth
      // ~180, where the vli-decoder return value decides decode success)
      // mark genuine unmodeled divergence: admit conservatively so the
      // coverage-gaining population past them is not lost.
      constexpr uint32_t kOpaqueFollowDepth = 64;
      if (current.depth < kOpaqueFollowDepth) {
        NodeRef next = current.child[0] != kUnexplored
                           ? current.child[0]
                           : current.child[1];
        if (next == kTerminal) {
          *out_node = kUnexplored;
          *out_dir = 0;
          if (out_veto_depth) *out_veto_depth = current.depth;
          if (out_veto_node) *out_veto_node = cur;
          if (out_veto_dir) *out_veto_dir = 0;
          if (out_veto_kind) *out_veto_kind = 0;
          check_veto_terminal += 1;
          return false;
        }
        if (next == kUnexplored) {
          *out_node = cur;
          *out_dir = 0;
          check_admit_frontier += 1;
          return true;
        }
        cur = next;
        continue;
      }
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
      // Terminal vetoes at length/count-family nodes can be untrustworthy
      // (same-prefix candidates legitimately continue when their length
      // counter carries a symbolic shadow the traced path never had), but
      // downgrading them all admits ~97% no-op executions (measured: the
      // vetoed population's post-terminal suffix is empty 99.6% of the time),
      // so the veto stands; len_related is retained as diagnostic signal.
      *out_node = kUnexplored;
      *out_dir = 0;
      if (out_veto_depth) *out_veto_depth = current.depth;
      if (out_veto_node) *out_veto_node = cur;
      if (out_veto_dir) *out_veto_dir = dir;
      if (out_veto_kind) *out_veto_kind = 0;
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
      if (out_veto_depth) *out_veto_depth = current.depth;
      if (out_veto_node) *out_veto_node = cur;
      if (out_veto_dir) *out_veto_dir = dir;
      if (out_veto_kind) *out_veto_kind = 1;
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
