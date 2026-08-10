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
    case PKind::UMin: return "umin";
    case PKind::UMax: return "umax";
    case PKind::SMin: return "smin";
    case PKind::SMax: return "smax";
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
    case PKind::Ctlz: return "ctlz";
    case PKind::Cttz: return "cttz";
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
static inline uint32_t child_skip_cnt(const Node &parent, uint8_t parent_dir,
                                      bool constraint) {
  if (!parent.constraint) return parent.skipCnt + (constraint ? 0 : 1);
  if (constraint && parent_dir == 0) return parent.skipCnt;
  return parent.skipCnt + (constraint ? 1 : 2);
}

uint32_t Tree::InsertTrace(const std::vector<Event> &events,
                           const dfsan_label_info *table,
                           size_t table_labels,
                           const uint8_t *input, uint32_t len,
                           NodeRef *out_tail_node, uint8_t *out_tail_dir) {
  if (events.empty()) {
    if (out_tail_node) *out_tail_node = kUnexplored;
    if (out_tail_dir) *out_tail_dir = 0;
    return 0;
  }
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
    if (cn.unstable) {
      num_conflicts += 1;
      return 0;
    }
    uint64_t v = 0;
    bool evaluated = false;
    uint8_t edir;
    if (cn.pred.opaque || input == nullptr) {
      edir = ev.result ? 1 : 0;  // follow the recorded direction
    } else {
      evaluated = eval_predicate(pred_arena_, cn.pred, input, len, &v, &eval);
      edir = evaluated ? (v ? 1 : 0) : (ev.result ? 1 : 0);
    }
    if (cn.cid != ev.cid ||
        (!cn.constraint && evaluated && edir != (ev.result ? 1 : 0))) {
      node(cur).unstable = true;
      num_conflicts += 1;
      return 0;
    }
    trace_depth += 1;
    parent = cur;
    dir = edir;
    NodeRef nxt = node(parent).child[dir];
    // A constraint value-fork reuses the same stream frame only when the
    // candidate takes dir-0 into another constraint node. A dir-1 edge is the
    // pinned value's real successor; if that successor also happens to be a
    // constraint node, it is the next independent wire frame and must consume
    // the current event.
    bool reuse_constraint =
        cn.constraint && edir == 0 && nxt != kTerminal &&
        (nxt == kUnexplored || node(nxt).constraint);
    if (!reuse_constraint) {
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
    if (parent >= kRoot && parent < nodes_.size())
      node(parent).unstable = true;
    num_conflicts += 1;
    return 0;
  }

  if (i == events.size() && k == 0) {
    if (node(parent).child[dir] == kUnexplored) {
      // The trace ends exactly at this edge: the decision (or the pinned
      // constraint value) produced no further symbolic decisions, so the
      // branch terminates here.
      node(parent).child[dir] = kTerminal;
    }
    if (out_tail_node) *out_tail_node = parent;
    if (out_tail_dir) *out_tail_dir = dir;
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
      new_node.skipCnt = parent == kRoot
          ? (ev.constraint ? 0u : 1u)
          : child_skip_cnt(node(parent), dir, ev.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = ev.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
      if (pred.opaque) {
        num_opaque += 1;
        opaque_by_error[static_cast<size_t>(pred.error)] += 1;
        if (pred.error_op) opaque_by_op[pred.error_op] += 1;
        opaque_by_cid[ev.cid] += 1;
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

  // The trace's last event terminates here. For a constraint event this
  // records the pinned value's branch as terminal — the constraint node's
  // dir-1 edge is explored the moment the node is created (either by the
  // creating candidate's follow-up or by this terminal), so a later
  // same-value candidate walks into the recorded edge and never admits on
  // it. The value-fork direction (dir-0) of a chain node is untouched and
  // stays unexplored.
  node(parent).child[dir] = kTerminal;
  num_nodes += created;
  if (trace_depth > max_depth) max_depth = trace_depth;
  if (out_tail_node) *out_tail_node = parent;
  if (out_tail_dir) *out_tail_dir = dir;
  return created;
}

uint32_t Tree::InsertSuffix(NodeRef parent, uint8_t direction,
                            const std::vector<Event> &events,
                            const dfsan_label_info *table,
                            size_t table_labels, NodeRef *out_tail_node,
                            uint8_t *out_tail_dir) {
  if (parent < kRoot || parent >= nodes_.size() || direction > 1 ||
      node(parent).child[direction] != kUnexplored) {
    if (out_tail_node) *out_tail_node = kUnexplored;
    if (out_tail_dir) *out_tail_dir = 0;
    return 0;
  }
  num_traces += 1;
  for (const Event &ev : events) num_events += ev.count;

  if (events.empty()) {
    // The candidate produced no further symbolic decisions past this edge.
    // For a pinned constraint value (dir-1) this records the branch
    // terminating here; the value-fork direction (dir-0) of a constraint
    // node is only ever marked terminal when a candidate actually walked it
    // with no follow-up (any divergence would have been collected).
    // A constraint node's value-fork can never legitimately reach here: a
    // candidate that evaluates dir-0 at a constraint node re-emits its own
    // multi-successor decision event at the same stream position (suffix
    // capture starts at the parent's skipCnt), so its captured suffix always
    // contains that constraint event and is never empty. Reaching here on a
    // constraint node therefore means the decision was invisible for this
    // candidate (label==0, e.g. an EOF/zero-count read) — a
    // collection-completeness gap, not a real termination — so the edge
    // stays unexplored and the normal rCnt/rlimit budget governs it instead
    // of being hard-closed.
    if (!node(parent).constraint) {
      node(parent).child[direction] = kTerminal;
    }
    // The edge this insertion closed (or left unexplored on a constraint
    // value-fork) is parent->direction.
    if (out_tail_node) *out_tail_node = parent;
    if (out_tail_dir) *out_tail_dir = direction;
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
      new_node.skipCnt = child_skip_cnt(node(cur), dir, event.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = event.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
      if (pred.opaque) {
        num_opaque += 1;
        opaque_by_error[static_cast<size_t>(pred.error)] += 1;
        if (pred.error_op) opaque_by_op[pred.error_op] += 1;
        opaque_by_cid[event.cid] += 1;
      }
      NodeRef next = append(std::move(new_node));
      if (next == kUnexplored) return created;
      node(cur).child[dir] = next;
      cur = next;
      dir = event.result ? 1 : 0;
      created += 1;
    }
  }

  // The suffix's last event terminates here (see the InsertTrace tail
  // comment): a constraint tail records the pinned value's branch as
  // terminal — the constraint node's dir-1 edge is explored at creation.
  node(cur).child[dir] = kTerminal;
  num_nodes += created;
  if (node(cur).depth > max_depth) max_depth = node(cur).depth;
  if (out_tail_node) *out_tail_node = cur;
  if (out_tail_dir) *out_tail_dir = dir;
  return created;
}

bool Tree::CheckInput(const uint8_t *input, uint32_t len, NodeRef *out_node,
                      uint8_t *out_dir, uint8_t rlimit,
                      uint32_t *out_veto_depth, NodeRef *out_veto_node,
                      uint8_t *out_veto_dir, uint8_t *out_veto_kind,
                      uint8_t len_rlimit) {
  if (len_rlimit == 0) len_rlimit = rlimit;
  NodeRef cur = node(kRoot).child[0];
  uint32_t walked = 0;
  EvalStats eval_stats;
  auto finish_profile = [&](unsigned outcome, uint32_t depth) {
    if (!profile_) return;
    profile_check_node_visits += walked;
    profile_check_predicate_calls += eval_stats.predicate_calls;
    profile_check_computed_nodes += eval_stats.computed_nodes;
    profile_check_cache_hits += eval_stats.cache_hits;
    profile_check_read_nodes += eval_stats.read_nodes;
    profile_check_read_bytes += eval_stats.read_bytes;
    profile_check_exit_depth[outcome] += depth;
  };
  if (cur == kUnexplored) {
    *out_node = kUnexplored;
    *out_dir = 0;
    check_admit_empty += 1;
    finish_profile(0, 0);
    return true;
  }

  // The context persists across candidates (vectors amortized instead of
  // re-filled to the arena size per check; the per-check zero-fill of
  // values_/stamps_ was the profiled check cost at large arena sizes).
  EvalContext &eval = check_eval_;
  eval.Reset();
  while (true) {
    walked += 1;
    const Node &current = node(cur);
    if (debug_) {
      fprintf(stderr, "[eval] node=%u cid=%u skip=%u depth=%u cons=%d\n",
              cur, current.cid, current.skipCnt, current.depth,
              current.constraint ? 1 : 0);
      DebugPredicate(cur, input, len);
    }
    if (current.unstable) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_unstable += 1;
      finish_profile(1, walked);
      return true;
    }
    if (current.pred.opaque) {
      // An opaque predicate has no sound candidate-dependent direction.
      // Never infer one from child topology: doing so turns an unsupported
      // expression such as idx_merge into a fabricated terminal proof.
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_opaque += 1;
      finish_profile(1, walked);
      return true;
    }
    uint64_t v = 0;
    if (!eval_predicate(pred_arena_, current.pred, input, len, &v, &eval,
                        profile_ ? &eval_stats : nullptr)) {
      *out_node = kUnexplored;
      *out_dir = 0;
      check_admit_eval_failure += 1;
      finish_profile(2, walked);
      return true;
    }
    uint8_t dir = v ? 1 : 0;
    NodeRef next = current.child[dir];
    if (debug_) {
      fprintf(stderr, "[eval]   -> dir=%u next=%u (c0=%u c1=%u)\n", dir,
              next, current.child[0], current.child[1]);
    }
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
      finish_profile(4, walked);
      return false;
    }
    if (next == kUnexplored) {
      *out_node = cur;
      *out_dir = dir;
      const uint8_t edge_rlimit = current.constraint && current.len_related
                                       ? len_rlimit
                                       : rlimit;
      if (current.rCnt[dir] < edge_rlimit) {
        check_admit_frontier += 1;
        finish_profile(3, walked);
        return true;
      }
      if (out_veto_depth) *out_veto_depth = current.depth;
      if (out_veto_node) *out_veto_node = cur;
      if (out_veto_dir) *out_veto_dir = dir;
      if (out_veto_kind) *out_veto_kind = 1;
      check_veto_rlimit += 1;
      finish_profile(5, walked);
      return false;
    }
    cur = next;
  }
}

void Tree::Dump(const char *path) const {
  FILE *f = fopen(path, "w");
  if (!f) return;
  fprintf(f, "# pcbt tree dump v2\n");
  fprintf(f, "# node cid depth skipCnt constraint unstable len_related child0 child1 rcnt0 rcnt1\n");
  for (NodeRef ref = 0; ref < nodes_.size(); ++ref) {
    const Node &n = node(ref);
    fprintf(f, "%u %u %u %u %u %u %u %u %u %u %u\n", ref, n.cid,
            n.depth, n.skipCnt, n.constraint ? 1 : 0, n.unstable ? 1 : 0,
            n.len_related ? 1 : 0, n.child[0], n.child[1], n.rCnt[0],
            n.rCnt[1]);
  }
  fclose(f);
}

bool Tree::IsSaturated(uint8_t rlimit, uint8_t len_rlimit) const {
  if (len_rlimit == 0) len_rlimit = rlimit;
  NodeRef entry = node(kRoot).child[0];
  return entry != kUnexplored && IsSaturated(entry, rlimit, len_rlimit);
}

bool Tree::IsSaturated(NodeRef ref, uint8_t rlimit, uint8_t len_rlimit) const {
  const Node &current = node(ref);
  if (current.unstable) return false;
  if (current.pred.opaque) return false;
  for (uint8_t direction = 0; direction != 2; ++direction) {
    NodeRef next = current.child[direction];
    if (next == kTerminal) continue;
    if (next == kUnexplored) {
      const uint8_t edge_rlimit = current.constraint && current.len_related
                                       ? len_rlimit
                                       : rlimit;
      if (current.rCnt[direction] < edge_rlimit) return false;
      continue;
    }
    if (!IsSaturated(next, rlimit, len_rlimit)) return false;
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
    // A constraint frame represents one multi-successor decision. The tree
    // may contain several constraint nodes at this same stream position as a
    // value-fork chain (case1 -> case2 -> ...). Reuse this one logical event
    // while traversing that chain; consume it only after reaching an ordinary
    // node, terminal, or unexplored edge. This is the same position rule used
    // by InsertTrace's prefix walk and CheckInput's predicate routing.
    if (ev.constraint) {
      while (true) {
        const Node &constraint = node(cur);
        uint64_t v = 0;
        uint8_t dir = ev.result ? 1 : 0;
        if (!constraint.pred.opaque &&
            eval_predicate(pred_arena_, constraint.pred, input, len, &v,
                           &eval)) {
          dir = v ? 1 : 0;
        }
        if (constraint.cid != ev.cid) {
          if (debug_) DebugPredicate(cur, input, len);
          r.mismatch_node = cur;
          r.error = ReplayError::CidMismatch;
          r.event_index = i;
          r.expected_cid = constraint.cid;
          r.observed_cid = ev.cid;
          return false;
        }
        NodeRef next = constraint.child[dir];
        if (next == kTerminal) {
          if (logic < trace_total) {
            r.mismatch_node = cur;
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
          r.frontier_dir = dir;
          r.suffix_begin = logic;
          return false;
        }

        cur = next;
        // Only a false predicate (dir-0) entering another constraint node is
        // a value-fork continuation of this same multi-successor decision.
        // The true/pinned edge (dir-1) consumes this frame even when its
        // successor is itself a constraint node from the next wire frame.
        if (dir == 0 && node(cur).constraint) continue;
        return true;
      }
    }
    // Evaluate predicate before checking CID so an observed event at a new
    // frontier is accepted as the start of the suffix.  A CID mismatch at an
    // existing node is always a trace conflict, including when its evaluated
    // child is unexplored: the event stream has already drifted at this node.
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
    if (current.cid != ev.cid) {
      if (debug_) DebugPredicate(cur, input, len);
      r.mismatch_node = cur;
      r.error = ReplayError::CidMismatch;
      r.event_index = i;
      r.expected_cid = current.cid;
      r.observed_cid = ev.cid;
      return false;
    }
    r.direction_checked = true;
    if (dir != ev.result) {
      if (debug_) DebugPredicate(cur, input, len);
      r.mismatch_node = cur;
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
        r.mismatch_node = cur;
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
    r.mismatch_node = cur;
    r.event_index = i;
    r.error = ReplayError::TruncatedTrace;
    if (debug_) DebugPredicate(cur, input, len);
  }
  return r;
}

}  // namespace pcbt
