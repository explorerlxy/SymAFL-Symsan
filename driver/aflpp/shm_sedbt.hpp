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
// (admit; mutator may skip cov and run fsrv_san if a CONS_SAN pin
// changed). Uncertain = opaque / eval fail / unstable (admit).
enum class SuffixCmp : uint8_t {
  Same = 0,
  Explored = 1,
  Unexplored = 2,
  Uncertain = 3
};

struct SuffixWalkStats {
  uint64_t steps = 0;
  uint64_t evals = 0;
};

SuffixCmp suffix_vs_parent(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                           const uint8_t *parent, uint32_t plen,
                           const uint8_t *mut, uint32_t mlen,
                           SuffixWalkStats *stats = nullptr);

// Same topology format as sedbt::Tree::Dump (SYMAFL_TREE_DUMP).
void dump_shm_tree(const SedbtShm *shm, const char *path);

// Recompute suffix path-s on a closed terminal: keep only symbols from
// suffix nodes that still have an unexplored sibling. Readers of term_s_*
// do not lock. Returns 1 if SHM path-s changed, 0 if skipped / unchanged.
int refresh_suffix_path_s(SedbtShm *shm, uint32_t tail, uint8_t tdir);
bool try_lock_path_s_refresh(SedbtShm *shm);
void unlock_path_s_refresh(SedbtShm *shm);
bool reserve_s_offs(SedbtShm *shm, uint32_t n, uint32_t *out_off);

void *create_shm(const char *name, size_t bytes, int *fd_out);
void *open_shm(const char *name, size_t bytes, int *fd_out);
// 1TiB virtual tree (memfd). Does not memset the mapping.
void *create_tree_shm(uint64_t bytes, int *fd_out);
void *map_tree_fd(int fd, uint64_t bytes);
bool send_fd(int sock, int fd);
int recv_fd(int sock);

}  // namespace symafl
