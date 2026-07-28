#include "pcbt.hpp"

namespace pcbt {

uint32_t Tree::InsertTrace(const std::vector<Event> &events,
                           rgd::RGDAstParser *parser) {
  if (events.empty()) return 0;
  num_traces += 1;
  num_events += events.size();

  Node *cur = &root_;
  size_t i = 0;
  uint64_t depth = 0;

  // Walk the existing trie prefix. Stop at the first missing child
  // (divergence point) or on a path conflict (discard the trace).
  for (; i < events.size(); i++) {
    uint8_t d = events[i].result ? 1 : 0;
    Node *nxt = cur->child[d];
    if (!nxt) break;                       // frontier: insert from here
    if (nxt->cid != events[i].cid) {       // conflict: same decision prefix
      num_conflicts += 1;                  // but different next branch site
      return 0;
    }
    cur = nxt;
    depth += 1;
  }

  // Append the remaining events as a fresh chain.
  uint32_t created = 0;
  for (; i < events.size(); i++) {
    auto node = std::make_unique<Node>();
    node->cid = events[i].cid;
    node->id = next_id_++;
    try {
      node->pred = parser->materialize(events[i].label);
    } catch (const std::exception &) {
      node->pred = nullptr;  // unparsable predicate: keep node, mark opaque
    }
    uint8_t d = events[i].result ? 1 : 0;
    Node *raw = node.get();
    arena_.push_back(std::move(node));
    cur->child[d] = raw;
    cur = raw;
    created += 1;
    depth += 1;
  }

  num_nodes += created;
  if (depth > max_depth) max_depth = depth;
  return created;
}

}  // namespace pcbt
