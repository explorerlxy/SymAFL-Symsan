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
    if (!nxt) {
      if (parent->terminal[dir]) {
        num_conflicts += 1;
        return 0;
      }
      break;
    }
    if (nxt->cid != events[i].cid) {
      num_conflicts += 1;
      return 0;
    }
    parent = nxt;
    dir = events[i].result ? 1 : 0;
    depth += 1;
  }

  // A complete replay that ends after an already-known node has explored its
  // outgoing edge. If the edge already has a successor, preserve that richer
  // path; deterministic targets do not produce both forms for one edge.
  if (i == events.size()) {
    if (!parent->child[dir]) parent->terminal[dir] = true;
    return 0;
  }

  // Append the remaining events as a fresh chain. All new predicates of
  // this trace share one arena (maximal DAG reuse via label memoization).
  RunConverter conv(table, table_labels);
  uint32_t created = 0;
  for (; i < events.size(); i++) {
    auto node = std::make_unique<Node>();
    node->cid = events[i].cid;
    node->id = next_id_++;
    node->depth = parent == &root_ ? 1 : parent->depth + 1;
    node->pred = conv.conv(events[i].label);
    if (node->pred.opaque) num_opaque += 1;
    Node *raw = node.get();
    arena_.push_back(std::move(node));
    parent->child[dir] = raw;
    parent->terminal[dir] = false;
    parent = raw;
    dir = events[i].result ? 1 : 0;
    created += 1;
    depth += 1;
  }

  // The replay completed after the final symbolic condition. Record that its
  // selected edge is explored even though it has no next symbolic node.
  parent->terminal[dir] = true;

  num_nodes += created;
  if (depth > max_depth) max_depth = depth;
  return created;
}

uint32_t Tree::InsertSuffix(Node *parent, uint8_t direction,
                            const std::vector<Event> &events,
                            const dfsan_label_info *table,
                            size_t table_labels) {
  if (!parent || direction > 1) return 0;

  num_traces += 1;
  num_events += events.size();

  // The caller owns the PCBT-prefix invariant. Do not replay or validate that
  // prefix here: suffix insertion is the direct equivalent of InsertTrace.
  if (events.empty()) {
    parent->terminal[direction] = true;
    return 0;
  }

  RunConverter conv(table, table_labels);
  uint32_t created = 0;
  uint8_t dir = direction;
  Node *cur = parent;
  for (const Event &event : events) {
    auto node = std::make_unique<Node>();
    node->cid = event.cid;
    node->id = next_id_++;
    node->depth = cur->depth + 1;
    node->pred = conv.conv(event.label);
    if (node->pred.opaque) num_opaque += 1;
    Node *raw = node.get();
    arena_.push_back(std::move(node));
    cur->child[dir] = raw;
    cur->terminal[dir] = false;
    cur = raw;
    dir = event.result ? 1 : 0;
    created += 1;
  }

  cur->terminal[dir] = true;
  num_nodes += created;
  if (cur->depth > max_depth) max_depth = cur->depth;
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
      if (cur->terminal[d]) {
        *out_node = nullptr;
        *out_dir = 0;
        return false;
      }
      // frontier in direction d
      *out_node = cur;
      *out_dir = d;
      return cur->rCnt[d] < rlimit;
    }
    cur = nxt;
  }
}

bool Tree::IsSaturated(uint32_t rlimit) const {
  return root_.child[0] && IsSaturated(root_.child[0], rlimit);
}

bool Tree::IsSaturated(const Node *node, uint32_t rlimit) const {
  if (!node || !node->pred.arena || node->pred.opaque) return false;

  for (uint8_t direction = 0; direction != 2; ++direction) {
    const Node *next = node->child[direction];
    if (next) {
      if (!IsSaturated(next, rlimit)) return false;
    } else if (!node->terminal[direction] && node->rCnt[direction] < rlimit) {
      return false;
    }
  }
  return true;
}

}  // namespace pcbt
