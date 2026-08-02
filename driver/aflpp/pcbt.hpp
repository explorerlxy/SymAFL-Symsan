// Path Constraint Binary Tree (PCBT) for SymAFL v2.
//
// A binary decision trie over symbolic-branch outcomes. Nodes live in a
// contiguous Tree-owned arena and refer to children by 32-bit NodeRef values:
// 0 is unexplored and 1 is the single global terminal node. The virtual root
// has no predicate; root.child[0] is the entry slot for the first condition.
#pragma once

#include <array>
#include <cstdint>
#include <unordered_map>
#include <vector>

#include "dfsan/dfsan.h"
#include "pred.hpp"

namespace pcbt {

using NodeRef = uint32_t;
constexpr NodeRef kUnexplored = 0;
constexpr NodeRef kTerminal = 1;
constexpr NodeRef kRoot = 2;

struct Node {
  uint32_t cid = 0;  // compile-time branch id
  Predicate pred;    // root view into Tree::pred_arena_
  NodeRef child[2] = {kUnexplored, kUnexplored};
  uint32_t depth = 0;                // root's children = 1
  uint8_t rCnt[2] = {0, 0};          // non-gaining admissions per direction
};

struct Event {
  uint32_t cid;
  uint32_t label;  // AST label in the *current* union table (per-run)
  uint8_t result;  // concrete branch outcome (0/1)
};

class Tree {
 public:
  Tree();

  // Insert one full branch-event path. The union table must still hold this
  // run's content. Returns the number of new topology nodes created.
  uint32_t InsertTrace(const std::vector<Event> &events,
                       const dfsan_label_info *table,
                       size_t table_labels);

  // Insert the suffix known to follow parent.child[direction]. The caller has
  // already established the PCBT prefix during screening, so this performs no
  // root replay or prefix matching. An empty suffix records the terminal node.
  uint32_t InsertSuffix(NodeRef parent, uint8_t direction,
                        const std::vector<Event> &events,
                        const dfsan_label_info *table, size_t table_labels);

  // Screen a candidate. On admission, *out_node / *out_dir identify an
  // unexplored frontier for retry bookkeeping and suffix skip depth. Terminal
  // edges are already explored and vetoed.
  bool CheckInput(const uint8_t *input, uint32_t len, NodeRef *out_node,
                  uint8_t *out_dir, uint8_t rlimit);

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
  };
  ReplayReport ReplayFullTrace(const std::vector<Event> &events,
                               const uint8_t *input, uint32_t len) const;

  bool IsSaturated(uint8_t rlimit) const;
  uint32_t depth(NodeRef ref) const { return node(ref).depth; }
  uint64_t num_pred_nodes() const { return pred_arena_.nodes.size(); }
  uint8_t &retry_count(NodeRef ref, uint8_t direction) {
    return node(ref).rCnt[direction];
  }
  uint8_t retry_count(NodeRef ref, uint8_t direction) const {
    return node(ref).rCnt[direction];
  }

  // stats
  uint64_t num_nodes = 0;
  uint64_t num_traces = 0;
  uint64_t num_events = 0;
  uint64_t num_conflicts = 0;
  uint64_t num_opaque = 0;
  uint64_t max_depth = 0;
  uint64_t check_admit_empty = 0;
  uint64_t check_admit_opaque = 0;
  uint64_t check_admit_eval_failure = 0;
  uint64_t check_admit_frontier = 0;
  uint64_t check_veto_terminal = 0;
  uint64_t check_veto_rlimit = 0;
  std::array<uint64_t, kPredErrorCount> opaque_by_error{};
  std::unordered_map<uint16_t, uint64_t> opaque_by_op;

 private:
  Node &node(NodeRef ref) { return nodes_[ref]; }
  const Node &node(NodeRef ref) const { return nodes_[ref]; }
  NodeRef append(Node &&node);
  bool IsSaturated(NodeRef ref, uint8_t rlimit) const;

  // Index 1 is a global terminal node; index 2 is the virtual root.
  std::vector<Node> nodes_;
  PredArena pred_arena_;
};

}  // namespace pcbt
