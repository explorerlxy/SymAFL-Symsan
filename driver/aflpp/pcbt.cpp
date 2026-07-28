#include "pcbt.hpp"

namespace pcbt {

uint32_t Tree::InsertTrace(const std::vector<Event> &events,
                           const dfsan_label_info *table,
                           size_t table_labels) {
  if (events.empty()) return 0;
  num_traces += 1;
  num_events += events.size();

  Node *parent = &root_;
  uint8_t dir = 0;  // entry slot: the first decision node is root_.child[0]
  uint64_t depth = 0;

  // Walk the existing trie; stop at the first missing child (insert point)
  // or bail out on a path conflict (cid mismatch at an existing node).
  size_t i = 0;
  for (; i < events.size(); i++) {
    Node *nxt = parent->child[dir];
    if (!nxt) break;
    if (nxt->cid != events[i].cid) {
      num_conflicts += 1;
      return 0;
    }
    parent = nxt;
    dir = events[i].result ? 1 : 0;
    depth += 1;
  }

  // Append the remaining events as a fresh chain. All new predicates of
  // this trace share one arena (maximal DAG reuse via label memoization).
  RunConverter conv(table, table_labels);
  uint32_t created = 0;
  for (; i < events.size(); i++) {
    auto node = std::make_unique<Node>();
    node->cid = events[i].cid;
    node->id = next_id_++;
    node->pred = conv.conv(events[i].label);
    if (node->pred.opaque) num_opaque += 1;
    Node *raw = node.get();
    arena_.push_back(std::move(node));
    parent->child[dir] = raw;
    parent = raw;
    dir = events[i].result ? 1 : 0;
    created += 1;
    depth += 1;
  }

  num_nodes += created;
  if (depth > max_depth) max_depth = depth;
  return created;
}

bool Tree::CheckInput(const uint8_t *input, uint32_t len, Node **out_node,
                      uint8_t *out_dir, uint32_t rlimit) {
  Node *cur = root_.child[0];
  if (!cur) {
    *out_node = nullptr;  // empty tree (bootstrap): admit all, no bookkeeping
    *out_dir = 0;
    return true;
  }

  while (true) {
    uint8_t d;
    if (!cur->pred.arena || cur->pred.opaque) {
      // cannot evaluate this node: conservative admit (no bookkeeping)
      *out_node = nullptr;
      *out_dir = 0;
      return true;
    }
    uint64_t v = 0;
    if (!eval_predicate(cur->pred, input, len, &v)) {
      d = 0;  // undefined (read past input end): v1's conservative rule
    } else {
      d = v ? 1 : 0;
    }
    Node *nxt = cur->child[d];
    if (!nxt) {
      // frontier in direction d
      *out_node = cur;
      *out_dir = d;
      return cur->rCnt[d] < rlimit;
    }
    cur = nxt;
  }
}

}  // namespace pcbt
