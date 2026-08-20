// Path Constraint Binary Tree (SEDBT) for SymAFL v2.
//
// A binary decision trie over symbolic-branch outcomes. Nodes live only in
// the process-wide SedbtShm. Tree is a writer: unpublished suffix chains are
// packed into that mapping, then the frontier child is store-released.
#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <unordered_map>
#include <vector>

#include "dfsan/dfsan.h"
#include "pred.hpp"
#include "analyzer_ipc.hpp"

namespace sedbt {

using NodeRef = uint32_t;
constexpr NodeRef kUnexplored = 0;
constexpr NodeRef kTerminal = 1;
constexpr NodeRef kRoot = 2;

// Event.constraint / ShmNode.constraint: 0 = ordinary branch,
// 1 = value pin (indcall target / read-length), 2 = tainted GEP index.
// Topology (skipCnt / value-fork) uses any non-zero; CONS_SAN binds only 2.
constexpr uint8_t kConstraintNone = 0;
constexpr uint8_t kConstraintPin = 1;
constexpr uint8_t kConstraintGep = 2;

// SYMAFL_MUT_PATH_S: 0/off = skip path-s; unset/1/suffix = suffix taint
// (LearnJob chain only); full/2 = full-path taint (root→terminal).
enum class PathSMode : uint8_t { Off = 0, Suffix = 1, Full = 2 };

inline PathSMode parse_mut_path_s_env(const char *e) {
  if (!e || !*e) return PathSMode::Suffix;
  if (e[0] == '0' && e[1] == '\0') return PathSMode::Off;
  if (std::strcmp(e, "off") == 0) return PathSMode::Off;
  if (std::strcmp(e, "full") == 0 || (e[0] == '2' && e[1] == '\0'))
    return PathSMode::Full;
  return PathSMode::Suffix;
}

inline const char *path_s_mode_name(PathSMode m) {
  switch (m) {
    case PathSMode::Off:
      return "off";
    case PathSMode::Full:
      return "full";
    default:
      return "suffix";
  }
}

struct Clause {
  uint32_t pred_root = 0;
  uint8_t negated = 0;
};

struct Closure {
  bool present = false;
  uint8_t trigger_neg = 0;  // 1 iff bug_dir == 0 (trigger is ¬pred)
  std::vector<uint32_t> s;
  std::vector<Clause> e;
};

struct Node {
  uint32_t cid = 0;  // compile-time branch id
  Predicate pred;    // root view into Tree::pred_arena_
  NodeRef child[2] = {kUnexplored, kUnexplored};
  uint32_t depth = 0;                // root's children = 1 (topology stats)
  // Event-stream position basis for suffix capture. Ordinary nodes store the
  // number of logical events through the node; constraint nodes store the
  // number before their event because a value-fork candidate re-emits that
  // constraint at the same position. A constraint child on dir-1 is a new
  // stream event and therefore advances by one; only a constraint child on a
  // constraint parent's dir-0 value-fork shares the parent's position.
  uint32_t skipCnt = 0;
  // This node is a constraint event (see skipCnt above). Its dir-1 subtree
  // describes only the pinned value's behavior; dir-0 is the value-fork
  // chain for candidates that pin a different value.
  bool constraint = false;
  // Tainted GEP-index pin (ShmNode.constraint == kConstraintGep). Indcall
  // and read-length pins are constraint but not gep_pin; CONS_SAN binds
  // only gep_pin offsets.
  bool gep_pin = false;
  // Prefix validation found incompatible symbolic event streams at this node.
  // Descendants are not safe terminal proofs while this flag is set.
  bool unstable = false;
  // The stored predicate's decision depends on a length/count family leaf
  // (Len/EofRead/Count/CountNeg1/CountElems). For constraint nodes this also
  // selects the optional length retry budget; terminal policy does not
  // downgrade these edges to admissions.
  bool len_related = false;
  // ADR 0010 W3: 0xff = not RSan; else the bug-trigger child direction.
  uint8_t rsan_bug_dir = 0xff;
  NodeRef parent = kUnexplored;
};

// Cached bug-edge closure: e does not contain trigger. Consume e ∪ {trigger}.
struct AttachedClosure {
  NodeRef node = kUnexplored;
  uint8_t bug_dir = 0xff;
  uint8_t trigger_neg = 0;
  uint32_t trigger_root = 0;
  std::vector<uint32_t> s;
  std::vector<Clause> e;
};

// Ancestor on the inserting/walking path (not including the target RSan node).
struct ClosureAncestor {
  uint32_t pred_root = 0;
  uint8_t taken_dir = 0;
  uint8_t rsan_bug_dir = 0xff;
  uint8_t trigger_neg = 0;
  bool usable = true;  // false: opaque / tautology / constraint pin (pred
                       // stays out of e; symbols still enter s)
  const Closure *cached = nullptr;
};

// Worklist slice (ADR 0010). ancestors are root→parent of N.
bool build_closure(const PNode *preds, size_t n_preds, uint32_t trigger_root,
                   uint8_t trigger_neg,
                   const std::vector<ClosureAncestor> &ancestors,
                   Closure *out);

bool eval_e_use(const PNode *preds, size_t n_preds, const AttachedClosure &c,
                const uint8_t *input, uint32_t len);
bool eval_e_use(const PredArena &arena, const AttachedClosure &c,
                const uint8_t *input, uint32_t len);

struct Event {
  uint32_t cid;
  uint32_t label;  // AST label in the *current* union table (per-run)
  uint8_t result;  // concrete branch outcome (0/1)
  // Constraint events (tainted GEP index / indcall target / read-length ==
  // concrete) have result always 1 and skip direction validation during
  // replay. 0 = ordinary, 1 = non-GEP pin, 2 = GEP index pin.
  uint8_t constraint = 0;
  // Fold frame: this event stands for `count` consecutive conditions that
  // share cid/result and a byte-advancing Read-family shape (getc loops,
  // flen_count loop bounds). 1 = plain event.
  uint16_t count = 1;
  // ADR 0010 W3: 0xff = not an RSan check; else bug-trigger direction 0/1.
  uint8_t rsan_bug_dir = 0xff;
};

class Tree {
 public:
  // Tests: anonymous SedbtShm. Analyzer: Tree(nullptr) then attach(shm).
  Tree();
  explicit Tree(std::nullptr_t);
  Tree(const Tree &) = delete;
  Tree &operator=(const Tree &) = delete;
  Tree(Tree &&o) noexcept;
  Tree &operator=(Tree &&o) noexcept;
  ~Tree();

  // Borrow the process-wide SedbtShm. Insert writes nodes/preds/closures
  // there and only then store-releases the frontier child (publish).
  void attach(void *sedbt_shm);
  void *shm() const { return shm_; }

  // Insert one full branch-event path evaluated against `input`. The union
  // table must still hold this run's content. Prefix matching is
  // predicate-evaluation-driven (symmetric with CheckInput): each existing
  // node's predicate is evaluated on the candidate input to choose the walk
  // direction, so a constraint node forks candidates that pin a different
  // value down its dir-0 value chain. Returns the number of new topology
  // nodes created.
  // On any insertion, *out_tail_node / *out_tail_dir (optional) receive the
  // last edge the trace closed (the edge marked terminal, or the edge where
  // the trace ended against the existing tree) — the edge a later veto
  // lands on; pair forensics records it as the inserting candidate's tree
  // position.
  uint32_t InsertTrace(const std::vector<Event> &events,
                       const dfsan_label_info *table, size_t table_labels,
                       const uint8_t *input, uint32_t len,
                       NodeRef *out_tail_node = nullptr,
                       uint8_t *out_tail_dir = nullptr);

  // Insert the suffix known to follow parent.child[direction]. The caller has
  // already established the SEDBT prefix during screening, so this performs no
  // root replay or prefix matching. An empty suffix on an ordinary edge
  // closes that edge terminal (the observed candidate's final decision);
  // constraint value-forks stay unexplored (a complete suffix can never be
  // empty there). Nonempty suffixes close their tail as terminal.
  // When the suffix inserts any node, *out_tail_node / *out_tail_dir
  // (optional) receive the LAST inserted edge — the edge that becomes
  // terminal (or that a later insertion continues from). This is the edge a
  // later veto lands on, so pair forensics records it as the inserting
  // candidate's tree position (the screening frontier can be shallower than
  // the terminal edge when the suffix has more than one event).
  uint32_t InsertSuffix(NodeRef parent, uint8_t direction,
                        const std::vector<Event> &events,
                        const dfsan_label_info *table, size_t table_labels,
                        const uint8_t *input, uint32_t len,
                        NodeRef *out_tail_node = nullptr,
                        uint8_t *out_tail_dir = nullptr);

  // Walk from parent.child[direction] on `input`. Frontier = still (or newly)
  // unexplored; Terminal = this candidate's path is already closed; Fail =
  // unstable / eval error. Used by the analyzer to retarget a LearnJob when
  // the recorded edge was filled by an earlier insert.
  enum class SuffixKind : uint8_t { Frontier = 0, Terminal = 1, Fail = 3 };
  struct SuffixHit {
    SuffixKind kind = SuffixKind::Fail;
    NodeRef frontier = kUnexplored;
    uint8_t dir = 0;
    uint32_t skip_cnt = 0;
  };
  SuffixHit CheckSuffix(NodeRef parent, uint8_t direction,
                        const uint8_t *input, uint32_t len) const;

  // Close an unexplored child as kTerminal (focused sanitizer crash on that
  // RSan bug edge). No-op if the child is already filled. Release-stores the
  // published parent child; no path-s.
  bool CloseUnexplored(NodeRef ref, uint8_t direction);

  // Screen a candidate. On admission, *out_node / *out_dir identify an
  // unexplored frontier for retry bookkeeping and suffix skip depth. Terminal
  // edges are already explored and vetoed. On veto, *out_veto_depth /
  // *out_veto_node identify the site and *out_veto_dir the evaluated
  // direction that hit the terminal/rlimit edge (pair forensics: the
  // admitted run recorded at (veto_node, veto_dir) walked the identical
  // path and created the terminal edge). *out_veto_kind classifies the veto:
  // 0 = terminal-class (the tree claims the decision trace terminates here -
  //   a probe-gained candidate here is evidence of a missed symbolic
  //   decision / TVBG), 1 = unused (rCnt/rlimit removed), 2 = unstable
  //   prefix (tree is not a safe terminal proof; probe gain is not TVBG).
  bool CheckInput(const uint8_t *input, uint32_t len, NodeRef *out_node,
                  uint8_t *out_dir, uint8_t rlimit,
                  uint32_t *out_veto_depth = nullptr,
                  NodeRef *out_veto_node = nullptr,
                  uint8_t *out_veto_dir = nullptr,
                  uint8_t *out_veto_kind = nullptr,
                  uint8_t len_rlimit = 0);

  // Const replay: walk the event vector from kRoot and compare CID order
  // and predicate directions against the tree.  Never mutates any state.
  // Returns a report describing structural agreement, mismatches, and the
  // first diagnostic position.
  enum class ReplayError : uint8_t {
    None, CidMismatch, DirectionMismatch, AfterTerminal, TruncatedTrace,
    InvalidEventResult,
  };
  struct ReplayReport {
    ReplayError error = ReplayError::None;
    size_t event_index = 0;          // first mismatch position
    size_t verified_events = 0;      // number of events that matched
    size_t suffix_begin = 0;         // first event beyond known prefix
    uint32_t expected_cid = 0;
    uint32_t observed_cid = 0;
    uint8_t evaluated_dir = 0;
    uint8_t observed_dir = 0;
    bool direction_checked = false;
    bool tree_empty = false;
    bool opaque_admission = false;
    bool eval_failure = false;
    bool reached_terminal = false;
    bool reached_frontier = false;
    NodeRef frontier_node = kUnexplored;
    uint8_t frontier_dir = 0;
    NodeRef mismatch_node = kUnexplored;
  };
  ReplayReport ReplayFullTrace(const std::vector<Event> &events,
                               const uint8_t *input, uint32_t len) const;

  uint32_t live_nodes() const { return live_n_; }
  uint32_t live_preds() const { return (uint32_t)pred_arena_.nodes.size(); }
  const PNode *pred_data() const { return pred_arena_.nodes.data(); }
  uint32_t pred_root_of(NodeRef ref) const;
  const Node &node_at(NodeRef ref) const;

  bool IsSaturated(uint8_t rlimit, uint8_t len_rlimit = 0) const;

  // Dump the tree topology (node id, cid, depth, skipCnt, constraint,
  // unstable, len_related, children) to a file for offline forensics.
  // kUnexplored=0 / kTerminal=1 / kRoot=2 are dumped verbatim.
  void Dump(const char *path) const;
  uint32_t depth(NodeRef ref) const;
  uint32_t cid_of(NodeRef ref) const;
  NodeRef root_child0() const;
  NodeRef child(NodeRef ref, uint8_t direction) const;
  uint32_t skip_of(NodeRef ref) const;
  bool is_constraint(NodeRef ref) const;
  bool is_len_related(NodeRef ref) const;
  uint8_t rsan_bug_dir_of(NodeRef ref) const;
  const Closure &closure_of(NodeRef ref) const;
  void collect_bug_closures(const uint8_t *input, uint32_t len,
                            std::vector<AttachedClosure> *out) const;
  bool eval_attached(const AttachedClosure &c, const uint8_t *input,
                     uint32_t len) const;
  bool is_unstable(NodeRef ref) const;
  void mark_unstable(NodeRef ref);
  uint32_t skip_for(NodeRef frontier_parent, uint8_t direction = 0) const;
  uint64_t num_pred_nodes() const { return pred_arena_.nodes.size(); }

  // Mismatch diagnostics (SYMAFL_SEDBT_DEBUG): dump the stored predicate at a
  // node (DAG + reads + the input bytes they reference) to stderr. Tree
  // members only; used by ReplayFullTrace's mismatch branches.
  void set_debug(bool enabled) { debug_ = enabled; }
  bool debug() const { return debug_; }
  void set_profile(bool enabled) { profile_ = enabled; }
  bool profile() const { return profile_; }
  // Retained no-op: rCnt/rlimit is removed; unexplored edges always admit
  // and saturation is terminal-closure only.
  void set_rlimit_unlimited(bool enabled) { rlimit_unlimited_ = enabled; }
  bool rlimit_unlimited() const { return rlimit_unlimited_; }
  // Conflict-site diagnostics (SYMAFL_CONFLICT_DIAG): log every InsertTrace
  // unstable mark / prefix-drift / already-unstable hit with node cid+depth.
  void set_conflict_diag(bool enabled) { diag_conflicts_ = enabled; }
  bool conflict_diag() const { return diag_conflicts_; }
  // Pair forensics: keep the first input that *created* each node so a later
  // cid/dir mismatch can dump the admit partner (not only the probe).
  // Disabled by default (memory); enable when anomaly/forensics dirs are set.
  void set_store_creators(bool enabled, uint32_t max_len = 65536) {
    store_creators_ = enabled;
    if (max_len) creator_max_len_ = max_len;
  }
  bool store_creators() const { return store_creators_; }
  // SYMAFL_MUT_PATH_S / SYMAFL_MUT_CLOSURE. Path-s: unset/`1`/`suffix` =
  // suffix taint, `full` = full-path taint, `0`/`off` = no mutation symbols
  // but constraint offsets are still bound root→terminal for CONS_SAN.
  void set_compute_path_s(bool enabled) {
    set_path_s_mode(enabled ? PathSMode::Suffix : PathSMode::Off);
  }
  bool compute_path_s() const { return path_s_mode_ != PathSMode::Off; }
  void set_path_s_mode(PathSMode m) {
    path_s_mode_ = m;
    compute_path_s_ = m != PathSMode::Off;
    if (shm_) shmp()->hdr.path_s_mode = (uint8_t)m;
  }
  PathSMode path_s_mode() const { return path_s_mode_; }
  void set_compute_closures(bool enabled) { compute_closures_ = enabled; }
  bool compute_closures() const { return compute_closures_; }
  void apply_mut_compute_env();
  // Copy creator input for `ref` into *out. Returns false if none stored.
  bool creator_of(NodeRef ref, std::vector<uint8_t> *out) const;
  void DebugPredicate(NodeRef ref, const uint8_t *input, uint32_t len) const;

  // stats
  uint64_t num_nodes = 0;
  uint64_t num_traces = 0;
  uint64_t num_events = 0;
  uint64_t num_conflicts = 0;
  uint64_t num_opaque = 0;     // residual converter-opaque (should stay ~0)
  uint64_t num_tautology = 0;  // fixed-direction constant decisions
  // Structural insert faults (policy A): insertion stops; no node written.
  // insert_structural_error == convert_fail + train_mismatch.
  uint64_t insert_structural_error = 0;
  uint64_t insert_struct_convert_fail = 0;   // converter opaque / unmodelable
  uint64_t insert_struct_train_mismatch = 0; // train eval != event.result
  // Per-CID census for structural faults (deinit prints top entries).
  std::unordered_map<uint32_t, uint64_t> struct_error_by_cid;
  uint64_t max_depth = 0;

  // Last structural fault detail for forensic capture (consumed by mutator).
  enum class StructFaultReason : uint8_t {
    None = 0,
    ConvertFail,
    TrainMismatch,
  };
  struct StructuralFault {
    StructFaultReason reason = StructFaultReason::None;
    uint32_t cid = 0;
    uint32_t label = 0;
    uint8_t result = 0;
    size_t event_index = 0;  // logical frame index in the insert stream
    bool from_suffix = false;
    bool pending = false;
  };
  // Pop the pending fault if any (clears pending). Returns true if a fault
  // was available.
  bool take_structural_fault(StructuralFault *out) {
    if (!last_struct_fault_.pending) return false;
    if (out) *out = last_struct_fault_;
    last_struct_fault_.pending = false;
    return true;
  }
  const StructuralFault &peek_structural_fault() const {
    return last_struct_fault_;
  }
  uint64_t check_admit_empty = 0;
  uint64_t check_admit_opaque = 0;  // DEPRECATED: opaque no longer whole-admits
  uint64_t check_follow_tautology = 0;  // walked through a tautology node
  uint64_t check_admit_eval_failure = 0;
  uint64_t check_admit_frontier = 0;
  uint64_t check_admit_len_veto = 0;  // terminal veto downgraded to admit
  uint64_t check_admit_unstable = 0;  // DEPRECATED: unstable nodes now veto
  uint64_t check_veto_terminal = 0;
  uint64_t check_veto_rlimit = 0;
  uint64_t check_veto_unstable = 0;  // replay-mismatch unstable node veto
  std::array<uint64_t, kPredErrorCount> opaque_by_error{};
  std::unordered_map<uint16_t, uint64_t> opaque_by_op;
  // Event-site census for opaque nodes. This is intentionally keyed by CID
  // rather than source text: the instrumentation build can emit a separate
  // CID map, while the mutator remains independent of debug information.
  std::unordered_map<uint32_t, uint64_t> opaque_by_cid;
  // CheckInput decomposition, populated only when profiling is enabled.
  uint64_t profile_check_node_visits = 0;
  uint64_t profile_check_predicate_calls = 0;
  uint64_t profile_check_computed_nodes = 0;
  uint64_t profile_check_cache_hits = 0;
  uint64_t profile_check_read_nodes = 0;
  uint64_t profile_check_read_bytes = 0;
  uint64_t profile_check_exit_depth[6] = {};

 private:
  symafl::ShmNode &at(NodeRef ref) {
    return ((symafl::SedbtShm *)shm_)->nodes[ref];
  }
  const symafl::ShmNode &at(NodeRef ref) const {
    return ((const symafl::SedbtShm *)shm_)->nodes[ref];
  }
  symafl::SedbtShm *shmp() { return (symafl::SedbtShm *)shm_; }
  const symafl::SedbtShm *shmp() const { return (const symafl::SedbtShm *)shm_; }
  NodeRef append(Node &&node);
  void maybe_store_creator(NodeRef ref, const uint8_t *input, uint32_t len);
  void finalize_closures(NodeRef tail, uint8_t tail_dir);
  void compute_closure(NodeRef n, const std::vector<std::pair<NodeRef, uint8_t>> &path);
  void commit_publish(NodeRef attach, uint8_t attach_dir, NodeRef first);
  // Suffix: mutation symbols after `frontier` (exclusive of frontier,
  // inclusive of tail). Full: walk tail→parent until kRoot.
  // Off: no mutation symbols; still bind root→terminal GEP-index offsets
  // as the whole slice (term_cons_n == term_s_n) so havoc CONS_SAN can
  // see a prefix GEP. Indcall/read-length pins stay out of term_cons_n.
  // Empty suffix has tail==frontier.
  void bind_path_s(NodeRef tail, uint8_t tdir, NodeRef frontier, uint8_t fdir);
  void publish_one_closure(const Closure &c, NodeRef ref);
  void finish_publish(NodeRef frontier, uint8_t fdir, NodeRef chain_first,
                      NodeRef tail, uint8_t tdir, bool close_term);
  void init_empty();
  bool IsSaturated(NodeRef ref, uint8_t rlimit, uint8_t len_rlimit) const;
  bool debug_ = false;
  bool profile_ = false;
  bool rlimit_unlimited_ = false;
  bool diag_conflicts_ = false;
  bool store_creators_ = false;
  bool compute_path_s_ = true;
  PathSMode path_s_mode_ = PathSMode::Suffix;
  bool compute_closures_ = true;
  uint32_t creator_max_len_ = 65536;
  StructuralFault last_struct_fault_{};
  mutable EvalContext check_eval_;

  void *shm_ = nullptr;  // symafl::SedbtShm*
  bool owns_shm_ = false;
  uint32_t live_n_ = kRoot + 1;
  uint32_t published_n_ = kRoot + 1;
  PredArena pred_arena_;
  std::unordered_map<NodeRef, std::vector<uint8_t>> creators_;
};

}  // namespace sedbt
