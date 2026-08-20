#include "shm_sedbt.hpp"

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstring>
#include <cstdio>

namespace symafl {

static uint32_t skip_for(const ShmNode &parent, uint8_t dir) {
  return parent.skipCnt + (parent.constraint && dir == 1 ? 1 : 0);
}

static void note_rsan(uint32_t cur, const ShmNode &n, WalkResult *r) {
  if (n.rsan_bug_dir <= 1) r->rsan_nodes.push_back(cur);
}

static void fill_terminal(const SedbtShm *shm, uint32_t last, uint8_t dir,
                          WalkResult *r) {
  r->learned = kWalkTerminal;
  r->last_node = last;
  r->last_dir = dir;
  const ShmNode &n = shm->nodes[last];
  r->path_s_ready = 1;
  r->path_s_off = n.term_s_off[dir];
  r->path_s_n = n.term_s_n[dir];
  r->path_s_cons_n = n.term_cons_n[dir];
  if (n.term_front[dir] >= sedbt::kRoot) {
    r->frontier = n.term_front[dir];
    r->dir = n.term_fdir[dir];
  }
}

static WalkResult walk_from(const SedbtShm *shm, uint32_t cur,
                            const uint8_t *input, uint32_t len) {
  WalkResult r{};
  r.learned = kWalkFailKind;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  const uint32_t n_preds = shm->hdr.n_preds.load(std::memory_order_acquire);
  if (cur == sedbt::kTerminal) {
    r.learned = kWalkTerminal;
    return r;
  }
  while (true) {
    if (cur == sedbt::kTerminal) {
      r.learned = kWalkTerminal;
      return r;
    }
    if (cur < sedbt::kRoot || cur >= n_nodes) {
      r.learned = kWalkFailKind;
      return r;
    }
    const ShmNode &n = shm->nodes[cur];
    if (n.unstable) {
      r.learned = kWalkFailKind;
      return r;
    }
    uint8_t dir = 0;
    if (n.pred_tautology || n.pred_opaque) {
      dir = n.pred_tautology ? n.pred_fixed_dir : 0;
    } else {
      sedbt::Predicate pred;
      pred.root = n.pred_root;
      pred.opaque = n.pred_opaque;
      pred.tautology = n.pred_tautology;
      pred.fixed_dir = n.pred_fixed_dir;
      uint64_t v = 0;
      if (!sedbt::eval_predicate(shm->preds, n_preds, pred, input, len, &v)) {
        r.learned = kWalkFailKind;
        return r;
      }
      dir = v ? 1 : 0;
    }
    note_rsan(cur, n, &r);
    uint32_t next = __atomic_load_n(&shm->nodes[cur].child[dir],
                                    __ATOMIC_ACQUIRE);
    if (next == sedbt::kUnexplored) {
      r.learned = kWalkFrontier;
      r.frontier = cur;
      r.dir = dir;
      r.skip_cnt = skip_for(n, dir);
      r.last_node = cur;
      r.last_dir = dir;
      return r;
    }
    if (next == sedbt::kTerminal) {
      fill_terminal(shm, cur, dir, &r);
      return r;
    }
    cur = next;
  }
}

void dump_shm_tree(const SedbtShm *shm, const char *path) {
  if (!shm || !path || !*path) return;
  FILE *f = fopen(path, "w");
  if (!f) return;
  const uint32_t n = shm->hdr.n_nodes.load(std::memory_order_acquire);
  fprintf(f, "# sedbt tree dump v2\n");
  fprintf(f, "# node cid depth skipCnt constraint unstable len_related "
             "child0 child1\n");
  for (uint32_t ref = 0; ref < n && ref < shm->hdr.node_cap; ++ref) {
    const ShmNode &sn = shm->nodes[ref];
    const uint32_t c0 =
        __atomic_load_n(&shm->nodes[ref].child[0], __ATOMIC_ACQUIRE);
    const uint32_t c1 =
        __atomic_load_n(&shm->nodes[ref].child[1], __ATOMIC_ACQUIRE);
    fprintf(f, "%u %u %u %u %u %u %u %u %u\n", ref, sn.cid, sn.depth,
            sn.skipCnt, sn.constraint ? 1u : 0u, sn.unstable ? 1u : 0u,
            sn.len_related ? 1u : 0u, c0, c1);
  }
  fclose(f);
}

WalkResult check_input(const SedbtShm *shm, const uint8_t *input,
                       uint32_t len) {
  WalkResult r{};
  r.learned = kWalkFailKind;
  if (!shm) return r;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  if (n_nodes <= sedbt::kRoot) {
    r.learned = kWalkFrontier;
    r.frontier = sedbt::kRoot;
    r.dir = 0;
    r.skip_cnt = 0;
    return r;
  }
  uint32_t cur = __atomic_load_n(&shm->nodes[sedbt::kRoot].child[0],
                                 __ATOMIC_ACQUIRE);
  if (cur == sedbt::kUnexplored) {
    r.learned = kWalkFrontier;
    r.frontier = sedbt::kRoot;
    r.dir = 0;
    r.skip_cnt = 0;
    return r;
  }
  if (cur == sedbt::kTerminal) {
    fill_terminal(shm, sedbt::kRoot, 0, &r);
    return r;
  }
  return walk_from(shm, cur, input, len);
}

WalkResult check_suffix(const SedbtShm *shm, const uint8_t *input, uint32_t len,
                        uint32_t frontier, uint8_t dir) {
  WalkResult r{};
  r.learned = kWalkFailKind;
  r.frontier = frontier;
  r.dir = dir;
  if (!shm || dir > 1) return r;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  if (frontier == sedbt::kRoot) {
    return check_input(shm, input, len);
  }
  if (frontier < sedbt::kRoot || frontier >= n_nodes) return r;
  const ShmNode &fn = shm->nodes[frontier];
  r.skip_cnt = skip_for(fn, dir);
  uint32_t next =
      __atomic_load_n(&shm->nodes[frontier].child[dir], __ATOMIC_ACQUIRE);
  if (next == sedbt::kUnexplored) {
    r.learned = kWalkFrontier;
    return r;
  }
  if (next == sedbt::kTerminal) {
    fill_terminal(shm, frontier, dir, &r);
    return r;
  }
  return walk_from(shm, next, input, len);
}

namespace {

// 0/1 = direction; <0 opaque (-2) or fail/unstable (-1).
int eval_dir(const SedbtShm *shm, uint32_t n_preds, uint32_t cur,
             const uint8_t *input, uint32_t len) {
  const ShmNode &n = shm->nodes[cur];
  if (n.unstable) return -1;
  if (n.pred_opaque) return -2;
  if (n.pred_tautology) return n.pred_fixed_dir ? 1 : 0;
  sedbt::Predicate pred;
  pred.root = n.pred_root;
  pred.opaque = 0;
  pred.tautology = 0;
  pred.fixed_dir = n.pred_fixed_dir;
  uint64_t v = 0;
  if (!sedbt::eval_predicate(shm->preds, n_preds, pred, input, len, &v))
    return -1;
  return v ? 1 : 0;
}

uint32_t first_child(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                     uint32_t n_nodes) {
  if (frontier == sedbt::kRoot) {
    return __atomic_load_n(&shm->nodes[sedbt::kRoot].child[0],
                           __ATOMIC_ACQUIRE);
  }
  if (frontier < sedbt::kRoot || frontier >= n_nodes || dir > 1)
    return sedbt::kUnexplored;
  return __atomic_load_n(&shm->nodes[frontier].child[dir], __ATOMIC_ACQUIRE);
}

uint8_t dir_bit(const SuffixScreenCache *c, uint32_t i) {
  return (c->bits[i >> 3] >> (i & 7)) & 1;
}

void push_dir_bit(SuffixScreenCache *c, uint8_t d) {
  if ((c->n & 7) == 0) c->bits.push_back(0);
  if (d) c->bits[c->n >> 3] |= (uint8_t)(1u << (c->n & 7));
  c->n += 1;
}

}  // namespace

void suffix_screen_cache_clear(SuffixScreenCache *c) {
  if (!c) return;
  *c = SuffixScreenCache{};
}

bool suffix_screen_cache_build(SuffixScreenCache *c, const SedbtShm *shm,
                               uint32_t frontier, uint8_t dir,
                               const uint8_t *parent, uint32_t plen) {
  suffix_screen_cache_clear(c);
  if (!c || !shm || !parent || dir > 1) return false;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  const uint32_t n_preds = shm->hdr.n_preds.load(std::memory_order_acquire);
  uint32_t cur = first_child(shm, frontier, dir, n_nodes);
  if (cur == sedbt::kTerminal) {
    c->frontier = frontier;
    c->dir = dir;
    return true;
  }
  if (cur == sedbt::kUnexplored || cur < sedbt::kRoot || cur >= n_nodes)
    return false;
  uint32_t steps = 0;
  while (steps++ < n_nodes) {
    if (cur < sedbt::kRoot || cur >= n_nodes) {
      suffix_screen_cache_clear(c);
      return false;
    }
    int dp = eval_dir(shm, n_preds, cur, parent, plen);
    if (dp < 0) {
      suffix_screen_cache_clear(c);
      return false;
    }
    push_dir_bit(c, (uint8_t)dp);
    uint32_t next = __atomic_load_n(&shm->nodes[cur].child[(uint8_t)dp],
                                    __ATOMIC_ACQUIRE);
    if (next == sedbt::kTerminal) break;
    if (next == sedbt::kUnexplored) break;
    cur = next;
  }
  c->frontier = frontier;
  c->dir = dir;
  return true;
}

static SuffixCmp suffix_walk_uncached(const SedbtShm *shm, uint32_t frontier,
                                      uint8_t dir, const uint8_t *parent,
                                      uint32_t plen, const uint8_t *mut,
                                      uint32_t mlen, SuffixWalkStats *stats) {
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  const uint32_t n_preds = shm->hdr.n_preds.load(std::memory_order_acquire);
  uint32_t cur = first_child(shm, frontier, dir, n_nodes);
  if (cur == sedbt::kTerminal) return SuffixCmp::Same;
  if (cur == sedbt::kUnexplored) return SuffixCmp::Uncertain;
  uint32_t steps = 0;
  while (steps++ < n_nodes) {
    if (cur < sedbt::kRoot || cur >= n_nodes) return SuffixCmp::Uncertain;
    int dp = eval_dir(shm, n_preds, cur, parent, plen);
    int dm = eval_dir(shm, n_preds, cur, mut, mlen);
    if (stats) {
      stats->steps += 1;
      stats->evals += 2;
    }
    if (dp < 0 || dm < 0) return SuffixCmp::Uncertain;
    if (dp != dm) {
      uint32_t taken = __atomic_load_n(&shm->nodes[cur].child[(uint8_t)dm],
                                       __ATOMIC_ACQUIRE);
      if (taken == sedbt::kUnexplored) return SuffixCmp::Unexplored;
      return SuffixCmp::Explored;
    }
    uint32_t next = __atomic_load_n(&shm->nodes[cur].child[(uint8_t)dp],
                                    __ATOMIC_ACQUIRE);
    if (next == sedbt::kTerminal) return SuffixCmp::Same;
    if (next == sedbt::kUnexplored) return SuffixCmp::Unexplored;
    cur = next;
  }
  return SuffixCmp::Uncertain;
}

SuffixCmp suffix_vs_parent(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                           const uint8_t *parent, uint32_t plen,
                           const uint8_t *mut, uint32_t mlen) {
  if (!shm || !parent || !mut || dir > 1) return SuffixCmp::Uncertain;
  return suffix_walk_uncached(shm, frontier, dir, parent, plen, mut, mlen,
                              nullptr);
}

SuffixCmp suffix_vs_parent_cached(const SedbtShm *shm,
                                  const SuffixScreenCache *cache,
                                  const uint8_t *mut, uint32_t mlen,
                                  SuffixWalkStats *stats) {
  if (!shm || !cache || !mut || cache->dir > 1) return SuffixCmp::Uncertain;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  const uint32_t n_preds = shm->hdr.n_preds.load(std::memory_order_acquire);
  uint32_t cur = first_child(shm, cache->frontier, cache->dir, n_nodes);
  if (cur == sedbt::kTerminal) return SuffixCmp::Same;
  if (cur == sedbt::kUnexplored) return SuffixCmp::Uncertain;
  if (cache->n == 0) return SuffixCmp::Uncertain;
  if (((cache->n + 7) >> 3) > cache->bits.size()) return SuffixCmp::Uncertain;
  for (uint32_t i = 0; i < cache->n; ++i) {
    if (cur < sedbt::kRoot || cur >= n_nodes) return SuffixCmp::Uncertain;
    const uint8_t dp = dir_bit(cache, i);
    int dm = eval_dir(shm, n_preds, cur, mut, mlen);
    if (stats) {
      stats->steps += 1;
      stats->evals += 1;
    }
    if (dm < 0) return SuffixCmp::Uncertain;
    if (dm != (int)dp) {
      uint32_t taken = __atomic_load_n(&shm->nodes[cur].child[(uint8_t)dm],
                                       __ATOMIC_ACQUIRE);
      if (taken == sedbt::kUnexplored) return SuffixCmp::Unexplored;
      return SuffixCmp::Explored;
    }
    uint32_t next = __atomic_load_n(&shm->nodes[cur].child[dp],
                                    __ATOMIC_ACQUIRE);
    if (next == sedbt::kTerminal) return SuffixCmp::Same;
    if (next == sedbt::kUnexplored) return SuffixCmp::Unexplored;
    cur = next;
  }
  return SuffixCmp::Same;
}

void *create_shm(const char *name, size_t bytes, int *fd_out) {
  shm_unlink(name);
  int fd = shm_open(name, O_RDWR | O_CREAT | O_EXCL, 0600);
  if (fd < 0) return nullptr;
  if (ftruncate(fd, (off_t)bytes)) {
    close(fd);
    shm_unlink(name);
    return nullptr;
  }
  void *p = mmap(nullptr, bytes, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if (p == MAP_FAILED) {
    close(fd);
    shm_unlink(name);
    return nullptr;
  }
  memset(p, 0, bytes);
  if (fd_out) *fd_out = fd;
  return p;
}

void *open_shm(const char *name, size_t bytes, int *fd_out) {
  int fd = shm_open(name, O_RDWR, 0600);
  if (fd < 0) return nullptr;
  void *p = mmap(nullptr, bytes, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if (p == MAP_FAILED) {
    close(fd);
    return nullptr;
  }
  if (fd_out) *fd_out = fd;
  return p;
}

}  // namespace symafl
