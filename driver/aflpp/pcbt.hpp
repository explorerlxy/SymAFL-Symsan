// Path Constraint Binary Tree (PCBT) for SymAFL v2.
//
// A binary decision trie over symbolic-branch outcomes. Node N represents
// one branch decision point (compile-time id `cid`, predicate over input
// bytes); N->child[d] is the next decision node observed after outcome d.
// The virtual root's child[0] is the entry slot: the first symbolic branch
// of the program (deterministic targets always reach the same first
// symbolic branch, so all traces enter through one node).
//
// InsertTrace: walk from the root following the trace's (cid, result)
// sequence; at the first missing child append the remaining events as a
// chain (divergence-point insertion). A trace that meets an existing child
// with a different cid signals non-determinism or tracking loss and is
// discarded (v1 replay-mismatch semantics).
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
  uint32_t rCnt[2] = {0, 0};            // non-gaining admissions per direction
  uint32_t id = 0;                      // stable node id
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

  // Screen a candidate. Returns true to admit; on admission *out_node /
  // *out_dir identify the frontier (for rCnt bookkeeping). rlimit: max
  // non-gaining admissions per frontier direction before it is pruned.
  bool CheckInput(const uint8_t *input, uint32_t len, Node **out_node,
                  uint8_t *out_dir, uint32_t rlimit);

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
};

}  // namespace pcbt
