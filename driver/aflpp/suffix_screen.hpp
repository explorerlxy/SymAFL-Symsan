#pragma once

#include "analyzer_ipc.hpp"

namespace symafl {

void suffix_screen_dump_stats();

// Walk the unpublished parent suffix starting at `first` and store a
// (node, parent_dir) table. `parent_len` is the inserting seed length.
// n=0 in the table header is trivial admit. Returns 0 only if the arena
// is full (caller leaves tab_off=0 → suffix_vs_parent).
uint32_t suffix_screen_bind(SedbtShm *shm, uint32_t first, uint32_t n_nodes,
                            uint32_t parent_len);

// 1 = admit (Unexplored / opaque), 0 = skip (Same / Explored),
// -1 = no table (arena full / missing tab_off) → caller uses suffix_vs_parent.
int suffix_screen(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                  const uint8_t *mut);

}  // namespace symafl
