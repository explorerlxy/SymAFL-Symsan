#pragma once

#include "analyzer_ipc.hpp"
#include "sedbt.hpp"

namespace symafl {

WalkResult check_input(const SedbtShm *shm, const uint8_t *input, uint32_t len);

// Walk from frontier.child[dir]. If still unexplored, learned=kWalkFrontier
// and frontier/dir unchanged. If the edge is closed, walk the suffix.
// A walk to terminal copies the insert bind site (term_front/term_fdir)
// into WalkResult.frontier/dir when that edge stored one.
WalkResult check_suffix(const SedbtShm *shm, const uint8_t *input, uint32_t len,
                        uint32_t frontier, uint8_t dir);

// Path-s screen: lockstep parent vs mutant from the bind frontier
// (full-path mode passes kRoot; that starts at root.child[0]).
// Same = still on the parent suffix through terminal (skip).
// Explored = first disagreement is onto a filled child (skip now; do not
// keep walking that sibling looking for a later unexplored).
// Unexplored = first disagreement (or a shared edge) is still unexplored
// (admit; mutator may skip cov and run fsrv_san if a GEP-index pin
// changed). Uncertain = opaque / eval fail / unstable (admit).
enum class SuffixCmp : uint8_t {
  Same = 0,
  Explored = 1,
  Unexplored = 2,
  Uncertain = 3
};

// Parent suffix dirs, packed 1 bit/node, filled once per queue_get.
// Mutants still eval each node; they only skip re-evaluating the parent.
struct SuffixScreenCache {
  uint32_t frontier = 0;
  uint8_t dir = 0xff;
  uint32_t n = 0;
  std::vector<uint8_t> bits;
};

struct SuffixWalkStats {
  uint64_t steps = 0;
  uint64_t evals = 0;
};

void suffix_screen_cache_clear(SuffixScreenCache *c);
bool suffix_screen_cache_build(SuffixScreenCache *c, const SedbtShm *shm,
                               uint32_t frontier, uint8_t dir,
                               const uint8_t *parent, uint32_t plen);

SuffixCmp suffix_vs_parent(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                           const uint8_t *parent, uint32_t plen,
                           const uint8_t *mut, uint32_t mlen);

// Lockstep using cached parent dirs. Mutant is eval'd at every node.
// stats may be null.
SuffixCmp suffix_vs_parent_cached(const SedbtShm *shm,
                                  const SuffixScreenCache *cache,
                                  const uint8_t *mut, uint32_t mlen,
                                  SuffixWalkStats *stats);

// Same topology format as sedbt::Tree::Dump (SYMAFL_TREE_DUMP).
void dump_shm_tree(const SedbtShm *shm, const char *path);

void *create_shm(const char *name, size_t bytes, int *fd_out);
void *open_shm(const char *name, size_t bytes, int *fd_out);

}  // namespace symafl
