// Path Constraint Binary Tree (PCBT) for SymAFL v2.
//
// A binary decision trie over symbolic-branch outcomes. Node N represents
// one branch decision point (compile-time id `cid`, predicate over input
// bytes); N->child[d] is the next decision node observed after outcome d.
// The virtual root's child[0] is the entry slot: the first symbolic branch
// of the program (deterministic targets always reach the same first
// symbolic branch, so all traces enter through one node).
//
// An edge is either unexplored, points at the next symbolic node, or is a
// terminal edge: it has been observed to complete without another symbolic
// condition. `child[d] == nullptr && terminal[d]` denotes the latter.
//
// CheckInput: walk from the root evaluating each node's predicate against
// the candidate's bytes; the first missing child on the evaluated
// direction is a frontier — the candidate is admitted unless that
// direction's low-value counter (rCnt) is saturated.
#pragma once

#include <cstdint>
#include <memory>
#include <vector>

#include "dfsan/dfsan.h"
#include "pred.hpp"

namespace pcbt {

struct Node {
  uint32_t cid = 0;                     // compile-time branch id
  Predicate pred;                       // branch predicate (arena view)
  Node *child[2] = {nullptr, nullptr};  // child[d]: next decision after d
  bool terminal[2] = {false, false};    // explored edge with no next node
  uint32_t rCnt[2] = {0, 0};            // non-gaining admissions per direction
  uint32_t id = 0;                      // stable node id
  uint32_t depth = 0;                   // symbolic depth; root's children = 1
};

struct Event {
  uint32_t cid;
  uint32_t label;  // AST label in the *current* union table (per-run)
  uint8_t result;  // concrete branch outcome (0/1)
};

class Tree {
 public:
  Tree() = default;

  // Insert one full branch-event path. The union table must still hold this
  // run's content (predicates are materialized inline). Returns the number
  // of new nodes created (0 = nothing new / conflict / failure).
  uint32_t InsertTrace(const std::vector<Event> &events,
                       const dfsan_label_info *table,
                       size_t table_labels);

  // Insert the event suffix known to follow parent->child[direction]. The
  // caller has already established the PCBT prefix during screening, so this
  // performs no root replay or prefix matching. An empty suffix marks that
  // edge terminal.
  uint32_t InsertSuffix(Node *parent, uint8_t direction,
                        const std::vector<Event> &events,
                        const dfsan_label_info *table, size_t table_labels);

  // Screen a candidate. Returns true to admit; on admission *out_node /
  // *out_dir identify the frontier (for rCnt bookkeeping and suffix skip
  // depth via Node::depth). Terminal edges are already explored and vetoed.
  // rlimit is the maximum non-gaining admissions per frontier direction.
  bool CheckInput(const uint8_t *input, uint32_t len, Node **out_node,
                  uint8_t *out_dir, uint32_t rlimit);

  // True when every evaluable path through the current tree ends at an
  // explored edge or an rCnt-pruned frontier. Opaque predicates deliberately
  // keep screening alive: their inputs must remain conservatively admitted.
  bool IsSaturated(uint32_t rlimit) const;

  const Node *root() const { return &root_; }
  Node *root() { return &root_; }

  // stats
  uint64_t num_nodes = 0;
  uint64_t num_traces = 0;
  uint64_t num_events = 0;
  uint64_t num_conflicts = 0;
  uint64_t num_opaque = 0;
  uint64_t max_depth = 0;

 private:
  Node root_;  // virtual root: no predicate; child[0] = entry slot
  std::vector<std::unique_ptr<Node>> arena_;
  uint32_t next_id_ = 1;

  bool IsSaturated(const Node *node, uint32_t rlimit) const;
};

}  // namespace pcbt
