#include "pcbt.hpp"

namespace pcbt {

namespace {

// libxml2 dict.c sites whose order interleaves by heap pool/hash layout
// rather than by input-only decisions. Resolved via djbHash of
// "<abs-path>/dict.c:LINE:COL" for the Realworld build path used here, plus
// basename forms for portability when SourceInfo is shortened.
// Pairs historically: 233(AddString pool) <-> 865(Lookup okey/len),
// 301(QString pool) <-> 1108(QLookup). Emitting them as PCBT events creates
// rare cid_mismatch at equal depth without a true input-only omission.
static bool is_libxml_dict_layout_cid(uint32_t cid) {
  switch (cid) {
    // Full path .../libxml2/src/dict.c:LINE:COL (Realworld ko-clang builds)
    case 2643614513u:  // :233:6 pool freeness
    case 2644690445u:  // :301:6
    case 2650836764u:  // :862:9
    case 1578374895u:  // :865:18 lookup okey/len
    case 2651919230u:  // :936:9
    case 4189721270u:  // :1108:18
    case 1580602981u:  // :881:10 final-chain memcmp site (also soft-paired)
    // Basename dict.c:LINE:COL
    case 1186823932u:  // dict.c:233:6
    case 1187899864u:  // dict.c:301:6
    case 1194046183u:  // dict.c:862:9
    case 748925978u:   // dict.c:865:18
    case 1195128649u:  // dict.c:936:9
    case 2587710785u:  // dict.c:1108:18
    case 751154064u:   // dict.c:881:10
      return true;
    default:
      return false;
  }
}

// True when a CID mismatch is the known dict layout interleaving class.
static bool is_dict_layout_cid_pair(uint32_t expected, uint32_t observed) {
  return is_libxml_dict_layout_cid(expected) &&
         is_libxml_dict_layout_cid(observed);
}

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
    case PKind::FpAdd: return "fp_add";
    case PKind::FpSub: return "fp_sub";
    case PKind::FpMul: return "fp_mul";
    case PKind::FpDiv: return "fp_div";
    case PKind::FpRem: return "fp_rem";
    case PKind::FpNeg: return "fp_neg";
    case PKind::FpAbs: return "fp_abs";
    case PKind::FpSqrt: return "fp_sqrt";
    case PKind::FpRound: return "fp_round";
    case PKind::FpMin: return "fp_min";
    case PKind::FpMax: return "fp_max";
    case PKind::FpCopySign: return "fp_copysign";
    case PKind::FpIsNan: return "fp_is_nan";
    case PKind::FpIsInf: return "fp_is_inf";
    case PKind::FpIsFinite: return "fp_is_finite";
    case PKind::FpSignBit: return "fp_signbit";
    case PKind::FpLrint: return "fp_lrint";
    case PKind::FpTrunc: return "fp_trunc";
    case PKind::FpExt: return "fp_ext";
    case PKind::FpToUI: return "fp_to_ui";
    case PKind::FpToSI: return "fp_to_si";
    case PKind::FpToFP: return "ui_to_fp";
    case PKind::FpSIToFP: return "si_to_fp";
    case PKind::FpExp: return "fp_exp";
    case PKind::FpExp2: return "fp_exp2";
    case PKind::FpLog: return "fp_log";
    case PKind::FpLog2: return "fp_log2";
    case PKind::FpLog10: return "fp_log10";
    case PKind::FpLog1p: return "fp_log1p";
    case PKind::FpPow: return "fp_pow";
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
  fprintf(stderr,
          "[pcbt-dbg] node=%u cid=%u depth=%u opaque=%d tautology=%d fixed_dir=%u\n",
          ref, n.cid, n.depth, n.pred.opaque ? 1 : 0, n.pred.tautology ? 1 : 0,
          n.pred.fixed_dir);
  if (n.pred.opaque || n.pred.tautology) return;
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

// True when the DAG freezes a large absolute constant that is neither a
// Insertion classification (policy A for structural faults):
// - Converter opaque → StructConvertFail: STOP insert, no node.
// - Train-eval mismatch → StructTrainMismatch: STOP insert, no node.
// - Input-free constant decision that matches train → Tautology (fixed_dir).
// - Otherwise Accept as ordinary evaluable predicate.
// Absolute-address + input stays evaluable (D2-A); P2 must complete taint.
enum class InsertPredClass : uint8_t {
  Accept,
  Tautology,
  StructConvertFail,
  StructTrainMismatch,
};

static bool is_struct_fault(InsertPredClass cls) {
  return cls == InsertPredClass::StructConvertFail ||
         cls == InsertPredClass::StructTrainMismatch;
}

static InsertPredClass classify_inserted_predicate(
    PredArena &arena, Predicate *pred, const uint8_t *input, uint32_t len,
    uint8_t expected_result, uint64_t concrete_op1, uint64_t concrete_op2,
    const dfsan_label_info *table, size_t table_labels, uint32_t source_label) {
  if (pred == nullptr) return InsertPredClass::StructConvertFail;
  const uint8_t fixed = expected_result ? 1 : 0;

  // Conversion failure: runtime emitted a symbolic event we cannot model.
  if (pred->opaque) return InsertPredClass::StructConvertFail;

  const bool candidate_independent =
      pred->reads.empty() && !pred_has_len_kind(arena, *pred);

  if (input == nullptr) {
    // No training bytes: cannot self-check eval direction. Accept ordinary
    // predicates (unit tests / rare paths); only pure constants become
    // tautology with the wire-recorded direction.
    if (candidate_independent) {
      pred->tautology = true;
      pred->fixed_dir = fixed;
      pred->opaque = false;
      return InsertPredClass::Tautology;
    }
    return InsertPredClass::Accept;
  }

  uint64_t v = 0;
  bool ok = eval_predicate(arena, *pred, input, len, &v);
  uint8_t edir = (ok && v != 0) ? 1 : 0;
  if (!ok || edir != fixed) {
    // Incomplete pointer-diff / FSE size models often leave a path-local
    // constant bias (untainted ip advances) so train eval disagrees even
    // though the residual is input-dependent. Align both sides to the
    // ICmp's captured concrete operands; if still wrong, fail closed.
    if (calibrate_pointer_train_pred(arena, pred, input, len, fixed,
                                     concrete_op1, concrete_op2, table,
                                     table_labels, source_label)) {
      ok = eval_predicate(arena, *pred, input, len, &v);
      edir = (ok && v != 0) ? 1 : 0;
    }
    if (!ok || edir != fixed) {
      // Model disagrees with the same input that produced the event: structural
      // defect. Do not freeze a lying or un-evaluable node into the tree.
      return InsertPredClass::StructTrainMismatch;
    }
  }

  // Candidate-independent decision → tautology with unique direction.
  if (candidate_independent) {
    pred->tautology = true;
    pred->fixed_dir = fixed;
    pred->opaque = false;
    return InsertPredClass::Tautology;
  }

  return InsertPredClass::Accept;
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
      if (diag_conflicts_)
        fprintf(stderr,
                "[pcbt-conflict] walk hit already-unstable node=%u cid=%u "
                "depth=%u ev_cid=%u\n",
                cur, cn.cid, cn.depth, ev.cid);
      return 0;
    }
    uint64_t v = 0;
    bool evaluated = false;
    uint8_t edir;
    if (cn.pred.tautology) {
      edir = cn.pred.fixed_dir;
    } else if (cn.pred.opaque || input == nullptr) {
      edir = ev.result ? 1 : 0;  // follow the recorded direction
    } else {
      evaluated = eval_predicate(pred_arena_, cn.pred, input, len, &v, &eval);
      edir = evaluated ? (v ? 1 : 0) : (ev.result ? 1 : 0);
    }
    const bool cid_ok =
        cn.cid == ev.cid || is_dict_layout_cid_pair(cn.cid, ev.cid);
    if (!cid_ok ||
        (!cn.constraint && evaluated && edir != (ev.result ? 1 : 0))) {
      node(cur).unstable = true;
      num_conflicts += 1;
      if (diag_conflicts_)
        fprintf(stderr,
                "[pcbt-conflict] InsertTrace marks node=%u cid=%u depth=%u "
                "unstable (ev_cid=%u ev_res=%u eval_dir=%u)\n",
                cur, cn.cid, cn.depth, ev.cid, ev.result,
                evaluated ? (v ? 1 : 0) : 255);
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
    if (diag_conflicts_)
      fprintf(stderr,
              "[pcbt-conflict] InsertTrace prefix-drift marks parent=%u "
              "cid=%u depth=%u unstable (remaining events start at i=%zu)\n",
              parent, node(parent).cid, node(parent).depth, i);
    return 0;
  }

  if (i == events.size() && k == 0) {
    NodeRef ch = node(parent).child[dir];
    if (ch == kUnexplored) {
      // The trace ends exactly at this edge: the decision (or the pinned
      // constraint value) produced no further symbolic decisions, so the
      // branch terminates here.
      node(parent).child[dir] = kTerminal;
    } else if (ch != kTerminal && ch >= kRoot && ch < nodes_.size()) {
      // Complete stream ends on an edge already extended by a longer path.
      // A finished short execution must own a Terminal here (or must have
      // diverged earlier via a symbolic branch). Silent "prefix accept" hides
      // a collection/model hole and makes REPLAY_ALL TruncatedTrace the only
      // exposure. Mirror AfterTerminal: conflict + mark unstable, no insert.
      node(parent).unstable = true;
      num_conflicts += 1;
      if (diag_conflicts_)
        fprintf(stderr,
                "[pcbt-conflict] InsertTrace early-end marks parent=%u "
                "cid=%u depth=%u unstable (child=%u already extended; "
                "complete short stream has no Terminal edge)\n",
                parent, node(parent).cid, node(parent).depth, ch);
      if (out_tail_node) *out_tail_node = parent;
      if (out_tail_dir) *out_tail_dir = dir;
      return 0;
    }
    // ch == kTerminal: already closed, consistent.
    if (out_tail_node) *out_tail_node = parent;
    if (out_tail_dir) *out_tail_dir = dir;
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  bool structural_stop = false;

  // Diagnostics: detect label pollution (non-zero label but no input dependency)
  static bool label_pollution_diagnostics = getenv("SYMAFL_LABEL_POLLUTION_DEBUG") != nullptr;
  static uint32_t pollution_logged = 0;

  for (; i < events.size() && !structural_stop; ++i) {
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
    for (Predicate pred : preds) {
      uint64_t cop1 = 0, cop2 = 0;
      if (table && ev.label > 0 && ev.label < table_labels) {
        cop1 = table[ev.label].op1.i;
        cop2 = table[ev.label].op2.i;
      }
      const InsertPredClass cls = classify_inserted_predicate(
          pred_arena_, &pred, input, len, ev.result, cop1, cop2, table,
          table_labels, ev.label);
      if (is_struct_fault(cls)) {
        // Policy A: do not write a node; leave the frontier edge unexplored.
        insert_structural_error += 1;
        if (cls == InsertPredClass::StructConvertFail)
          insert_struct_convert_fail += 1;
        else
          insert_struct_train_mismatch += 1;
        struct_error_by_cid[ev.cid] += 1;
        if (pred.error != PredError::None) {
          opaque_by_error[static_cast<size_t>(pred.error)] += 1;
          if (pred.error_op) opaque_by_op[pred.error_op] += 1;
        }
        last_struct_fault_ = StructuralFault{
            cls == InsertPredClass::StructConvertFail
                ? StructFaultReason::ConvertFail
                : StructFaultReason::TrainMismatch,
            ev.cid,
            ev.label,
            ev.result,
            i,
            /*from_suffix=*/false,
            /*pending=*/true};
        if (diag_conflicts_) {
          fprintf(stderr,
                  "[pcbt-struct] InsertTrace stop reason=%s cid=%u label=%u "
                  "result=%u event_index=%zu created=%u\n",
                  cls == InsertPredClass::StructConvertFail ? "convert_fail"
                                                              : "train_mismatch",
                  ev.cid, ev.label, ev.result, i, created);
        }
        structural_stop = true;
        break;
      }
      Node new_node;
      new_node.cid = ev.cid;
      new_node.depth = parent == kRoot ? 1 : node(parent).depth + 1;
      new_node.skipCnt = parent == kRoot
          ? (ev.constraint ? 0u : 1u)
          : child_skip_cnt(node(parent), dir, ev.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = ev.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
      if (cls == InsertPredClass::Tautology) {
        num_tautology += 1;
      }
      NodeRef next = append(std::move(new_node));
      if (next == kUnexplored) return created;
      node(parent).child[dir] = next;
      parent = next;
      dir = pred.tautology ? pred.fixed_dir : (ev.result ? 1 : 0);
      created += 1;
      trace_depth += 1;
    }
  }

  // Close terminal only when the full remaining stream was inserted. A
  // structural stop leaves the current edge unexplored so later candidates
  // can still be admitted there once the model is fixed.
  if (!structural_stop) {
    node(parent).child[dir] = kTerminal;
  }
  num_nodes += created;
  if (trace_depth > max_depth) max_depth = trace_depth;
  if (out_tail_node) *out_tail_node = parent;
  if (out_tail_dir) *out_tail_dir = dir;
  return created;
}

uint32_t Tree::InsertSuffix(NodeRef parent, uint8_t direction,
                            const std::vector<Event> &events,
                            const dfsan_label_info *table,
                            size_t table_labels, const uint8_t *input,
                            uint32_t len, NodeRef *out_tail_node,
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
    if (node(parent).constraint) {
      // Constraint value-fork: a candidate walking a constraint node's
      // dir-0 re-emits its own multi-successor decision event at the same
      // stream position, so a complete suffix can never be empty here. An
      // empty suffix on a constraint parent is an incomplete-capture
      // boundary and must leave the value-fork unexplored (the rCnt/rlimit
      // budget governs mining); a different pinned value could still carry
      // further decisions.
      if (out_tail_node) *out_tail_node = parent;
      if (out_tail_dir) *out_tail_dir = direction;
      return 0;
    }
    // An empty suffix on an ordinary edge records the observed candidate's
    // final decision: it produced no further symbolic decision past this
    // edge, so the branch terminates here (identical to InsertTrace's
    // trace-ends-at-edge rule). Closing terminal is deliberate: if a later
    // same-prefix candidate carries symbolic events this candidate lost (a
    // collection gap - an invisible read, an early-terminating invalid
    // input, a length/count shadow absent for this candidate), it is vetoed
    // at this terminal and surfaces as terminal-veto-but-gain. Leaving the
    // edge unexplored would silently admit and re-insert those events,
    // self-healing the symptom while the omission stays invisible and the
    // tree silently diverges from the theoretical SEDBT tree. Exposure via
    // tvbg is preferred over silent divergence; the collection-gap repair
    // then fixes the root cause so the tree becomes correct instead of
    // merely consistent.
    if (out_tail_node) *out_tail_node = parent;
    if (out_tail_dir) *out_tail_dir = direction;
    node(parent).child[direction] = kTerminal;
    return 0;
  }

  RunConverter conv(table, table_labels, &pred_arena_);
  uint32_t created = 0;
  uint8_t dir = direction;
  NodeRef cur = parent;
  bool structural_stop = false;

  // Diagnostics: count events with empty reads (label pollution candidates)
  static bool label_pollution_diagnostics = getenv("SYMAFL_LABEL_POLLUTION_DEBUG") != nullptr;
  static uint32_t pollution_logged = 0;
  static uint32_t total_events_seen = 0;
  static uint32_t empty_reads_seen = 0;
  static bool diagnostics_banner_printed = false;

  for (const Event &event : events) {
    if (structural_stop) break;
    std::vector<Predicate> preds;
    if (event.count > 1) {
      conv.expand_fold(event.label, event.count, 0, &preds);
    } else {
      preds.push_back(conv.conv(event.label));
    }
    for (Predicate pred : preds) {
      total_events_seen++;
      uint64_t cop1 = 0, cop2 = 0;
      if (table && event.label > 0 && event.label < table_labels) {
        cop1 = table[event.label].op1.i;
        cop2 = table[event.label].op2.i;
      }
      const InsertPredClass cls = classify_inserted_predicate(
          pred_arena_, &pred, input, len, event.result, cop1, cop2, table,
          table_labels, event.label);

      if (!diagnostics_banner_printed) {
        if (label_pollution_diagnostics) {
          fprintf(stderr, "[label-pollution] diagnostics ENABLED\n");
        }
        diagnostics_banner_printed = true;
      }

      if (is_struct_fault(cls)) {
        insert_structural_error += 1;
        if (cls == InsertPredClass::StructConvertFail)
          insert_struct_convert_fail += 1;
        else
          insert_struct_train_mismatch += 1;
        struct_error_by_cid[event.cid] += 1;
        if (pred.error != PredError::None) {
          opaque_by_error[static_cast<size_t>(pred.error)] += 1;
          if (pred.error_op) opaque_by_op[pred.error_op] += 1;
        }
        last_struct_fault_ = StructuralFault{
            cls == InsertPredClass::StructConvertFail
                ? StructFaultReason::ConvertFail
                : StructFaultReason::TrainMismatch,
            event.cid,
            event.label,
            event.result,
            total_events_seen > 0 ? total_events_seen - 1 : 0,
            /*from_suffix=*/true,
            /*pending=*/true};
        if (diag_conflicts_) {
          fprintf(stderr,
                  "[pcbt-struct] InsertSuffix stop reason=%s cid=%u label=%u "
                  "result=%u created=%u\n",
                  cls == InsertPredClass::StructConvertFail ? "convert_fail"
                                                              : "train_mismatch",
                  event.cid, event.label, event.result, created);
        }
        structural_stop = true;
        break;
      }

      if (cls == InsertPredClass::Tautology && pred.reads.empty() &&
          !pred_has_len_kind(pred_arena_, pred)) {
        empty_reads_seen++;
        static FILE *poll_file = nullptr;
        static bool poll_file_checked = false;
        if (!poll_file_checked) {
          const char *log_path = getenv("SYMAFL_POLLUTION_LOG");
          if (!log_path) log_path = "/tmp/symafl_pollution.log";
          poll_file = fopen(log_path, "a");
          poll_file_checked = true;
        }
        if (poll_file && pollution_logged < 500) {
          fprintf(poll_file, "[label-pollution] #%u cid=%u label=%u result=%u\n",
                  pollution_logged, event.cid, event.label, event.result);
          fprintf(poll_file, "  label_info: op=0x%x l1=%u l2=%u size=%u op1=%llu op2=%llu\n",
                  table[event.label].op, table[event.label].l1, table[event.label].l2,
                  table[event.label].size,
                  (unsigned long long)table[event.label].op1.i,
                  (unsigned long long)table[event.label].op2.i);
          fflush(poll_file);
          pollution_logged++;
        }
      }

      Node new_node;
      new_node.cid = event.cid;
      new_node.depth = node(cur).depth + 1;
      new_node.skipCnt = child_skip_cnt(node(cur), dir, event.constraint != 0);
      new_node.pred = pred;
      new_node.constraint = event.constraint != 0;
      new_node.len_related = pred_has_len_kind(pred_arena_, pred);
      if (cls == InsertPredClass::Tautology) num_tautology += 1;
      NodeRef next = append(std::move(new_node));
      if (next == kUnexplored) return created;
      node(cur).child[dir] = next;
      cur = next;
      dir = pred.tautology ? pred.fixed_dir : (event.result ? 1 : 0);
      created += 1;
    }
  }

  // Terminal only if the full suffix was accepted (policy A).
  if (!structural_stop) {
    node(cur).child[dir] = kTerminal;
  }
  num_nodes += created;
  if (node(cur).depth > max_depth) max_depth = node(cur).depth;

  // Report label pollution statistics
  if (label_pollution_diagnostics && total_events_seen > 0) {
    static uint32_t last_report_total = 0;
    if (total_events_seen - last_report_total >= 10000) {
      fprintf(stderr, "[label-pollution] stats: total=%u empty_reads=%u (%.1f%%)\n",
              total_events_seen, empty_reads_seen,
              100.0 * empty_reads_seen / total_events_seen);
      last_report_total = total_events_seen;
    }
  }

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
      // Fail-closed: veto candidates routed through unstable nodes (those with
      // replay mismatches). Previously admitted them, causing admit_unstable to
      // count thousands of unverified admissions. An unstable node indicates a
      // trace/tree defect (missing decision, non-determinism, incomplete
      // predicate); admit would bypass the very verification SYMAFL_REPLAY_CHECK
      // was intended to enforce.
      if (out_veto_node) *out_veto_node = cur;
      if (out_veto_dir) *out_veto_dir = 0;
      if (out_veto_depth) *out_veto_depth = current.depth;
      if (out_veto_kind) *out_veto_kind = 0; // not a real terminal
      *out_node = cur;
      *out_dir = 0;
      check_veto_unstable += 1;
      finish_profile(3, walked);
      return false;
    }
    // Tautology: unique fixed direction (constant decision). Continue walk;
    // never whole-candidate admit. Legacy opaque is treated the same when
    // fixed_dir was recorded (should not remain after classify_inserted).
    if (current.pred.tautology || current.pred.opaque) {
      uint8_t dir = current.pred.tautology ? current.pred.fixed_dir : 0;
      if (current.pred.tautology) check_follow_tautology += 1;
      else check_admit_opaque += 1;  // legacy residual path (should be ~0)
      NodeRef next = current.child[dir];
      if (next == kTerminal) {
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
        if (rlimit_unlimited_ || current.rCnt[dir] < edge_rlimit) {
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
      continue;
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
      // rlimit-unlimited quality mode bypasses the retry budget entirely:
      // every candidate that reaches an unexplored edge is admitted, so an
      // exhausted rCnt can never mask a candidate's stream from the replay
      // census (and saturation is decided by terminal closure alone).
      if (rlimit_unlimited_ || current.rCnt[dir] < edge_rlimit) {
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
  // Tautology has a single meaningful direction; the other edge is ignored.
  if (current.pred.tautology) {
    NodeRef next = current.child[current.pred.fixed_dir];
    if (next == kTerminal) return true;
    if (next == kUnexplored) return false;
    return IsSaturated(next, rlimit, len_rlimit);
  }
  if (current.pred.opaque) return false;
  for (uint8_t direction = 0; direction != 2; ++direction) {
    NodeRef next = current.child[direction];
    if (next == kTerminal) continue;
    if (next == kUnexplored) {
      // With an unlimited retry budget an unexplored edge never saturates:
      // only terminal closure (or unstable/opaque) can saturate the tree.
      if (rlimit_unlimited_) return false;
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
        if (constraint.pred.tautology) {
          dir = constraint.pred.fixed_dir;
        } else if (!constraint.pred.opaque &&
                   eval_predicate(pred_arena_, constraint.pred, input, len, &v,
                                  &eval)) {
          dir = v ? 1 : 0;
        }
        if (constraint.cid != ev.cid) {
          // Path-local dict heap/hash interleaving: stop as a soft frontier
          // without counting a SEDBT cid conflict or marking the node unstable.
          if (is_dict_layout_cid_pair(constraint.cid, ev.cid)) {
            r.event_index = i;
            r.verified_events = logic > 0 ? logic - 1 : 0;
            r.reached_frontier = true;
            r.frontier_node = cur;
            r.frontier_dir = dir;
            r.suffix_begin = logic > 0 ? logic - 1 : 0;
            return false;
          }
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
          // A false edge of a constraint node is a value-fork refinement:
          // the observed constraint event must be re-emitted at the same
          // stream position when InsertSuffix mines this edge.  skip_for()
          // therefore returns the position before this logical event, while
          // ordinary and pinned constraint edges start after it.
          r.suffix_begin = logic - (ev.constraint && dir == 0 ? 1 : 0);
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
    // Tautology: follow fixed_dir (must match the stream event for a
    // consistent tree). Continue into the child like an ordinary step.
    if (current.pred.tautology) {
      uint8_t dir = current.pred.fixed_dir;
      if (current.cid != ev.cid) {
        if (is_dict_layout_cid_pair(current.cid, ev.cid)) {
          r.event_index = i;
          r.verified_events = logic > 0 ? logic - 1 : 0;
          r.reached_frontier = true;
          r.frontier_node = cur;
          r.frontier_dir = dir;
          r.suffix_begin = logic > 0 ? logic - 1 : 0;
          return false;
        }
        r.mismatch_node = cur;
        r.error = ReplayError::CidMismatch;
        r.event_index = i;
        r.expected_cid = current.cid;
        r.observed_cid = ev.cid;
        return false;
      }
      if ((ev.result ? 1 : 0) != dir) {
        r.mismatch_node = cur;
        r.error = ReplayError::DirectionMismatch;
        r.event_index = i;
        r.expected_cid = current.cid;
        r.observed_cid = ev.cid;
        r.evaluated_dir = dir;
        r.observed_dir = ev.result ? 1 : 0;
        r.direction_checked = true;
        return false;
      }
      NodeRef next = current.child[dir];
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
      return true;
    }
    if (current.pred.opaque) {
      // Legacy residual: treat like tautology using stream direction.
      r.event_index = i;
      r.verified_events = logic - 1;
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
      if (is_dict_layout_cid_pair(current.cid, ev.cid)) {
        r.event_index = i;
        r.verified_events = logic > 0 ? logic - 1 : 0;
        r.reached_frontier = true;
        r.frontier_node = cur;
        r.frontier_dir = dir;
        r.suffix_begin = logic > 0 ? logic - 1 : 0;
        return false;
      }
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
    // still expects more conditions on this walk. A complete short execution
    // must have its own Terminal edge; sharing a pure event-prefix with a
    // longer learned path without an earlier symbolic divergence is a
    // collection/insert defect (not a soft success). Surface as TruncatedTrace.
    r.verified_events = logic;
    r.mismatch_node = cur;
    r.event_index = i;
    r.error = ReplayError::TruncatedTrace;
    if (debug_) DebugPredicate(cur, input, len);
  }
  return r;
}

}  // namespace pcbt
