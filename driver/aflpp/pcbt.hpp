// Path Constraint Binary Tree (PCBT) for SymAFL v2.
//
// A trie over symbolic-branch decision sequences. Each tree node represents
// one symbolic branch decision point (compile-time branch id `cid`); its two
// children correspond to the two outcomes of the branch condition. A node
// stores the branch predicate as materialized on the trace that created the
// node (an rgd::AstNode over input bytes). Candidates are screened by
// evaluating predicates along the trie path (Phase 2); traces of executed
// inputs are inserted by walking the trie to the first missing child and
// appending the remaining event chain there (divergence-point insertion).
//
// The event stream of one traced execution always starts at program entry
// (SymSan emits one event per symbolic conditional branch, in execution
// order), so the trie root corresponds to the program's first symbolic
// branch decision.
#pragma once

#include <cstdint>
#include <memory>
#include <vector>

#include "ast.h"        // rgd::AstNode
#include "parse-rgd.h"  // rgd::RGDAstParser

namespace pcbt {

using expr_t = std::shared_ptr<rgd::AstNode>;

struct Node {
  uint32_t cid = 0;                     // compile-time branch id
  expr_t pred;                          // branch predicate (input-byte AST)
  Node *child[2] = {nullptr, nullptr};  // child[d]: path after outcome d
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

  // Insert one full branch-event path. Materializes predicates for newly
  // created nodes via parser.get_root_expr(label) (the union table must
  // still hold this run's content). On a path conflict (existing child with
  // a different cid — non-determinism or predicate approximation mismatch)
  // the trace is discarded and counted, mirroring v1's replay-mismatch
  // handling. Returns the number of new nodes created.
  uint32_t InsertTrace(const std::vector<Event> &events,
                       rgd::RGDAstParser *parser);

  const Node *root() const { return &root_; }
  Node *root() { return &root_; }

  // stats
  uint64_t num_nodes = 0;
  uint64_t num_traces = 0;
  uint64_t num_events = 0;
  uint64_t num_conflicts = 0;
  uint64_t max_depth = 0;

 private:
  Node root_;  // virtual root: cid=0, no predicate
  std::vector<std::unique_ptr<Node>> arena_;
  uint32_t next_id_ = 1;
};

}  // namespace pcbt
