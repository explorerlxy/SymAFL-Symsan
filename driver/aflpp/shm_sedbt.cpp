#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include "shm_sedbt.hpp"

#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <unistd.h>
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <unordered_set>
#include <vector>

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
  const ShmNode &n = shm_nodes(shm)[last];
  r->path_s_ready = 1;
  r->path_s_off = __atomic_load_n(&n.term_s_off[dir], __ATOMIC_ACQUIRE);
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
  // Do not load n_nodes/n_preds per step. commit_publish stores n_preds,
  // n_nodes, then the frontier child (release). An acquire of child[dir]
  // already sees that node and its pred DAG. node_cap/pred_cap are fixed
  // at layout (mmap hard bound).
  const uint32_t node_cap = shm->hdr.node_cap;
  const uint32_t pred_cap = shm->hdr.pred_cap;
  if (cur == sedbt::kTerminal) {
    r.learned = kWalkTerminal;
    return r;
  }
  while (true) {
    if (cur == sedbt::kTerminal) {
      r.learned = kWalkTerminal;
      return r;
    }
    if (cur < sedbt::kRoot || cur >= node_cap) {
      r.learned = kWalkFailKind;
      return r;
    }
    const ShmNode &n = shm_nodes(shm)[cur];
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
      if (!sedbt::eval_predicate(shm_preds(shm), pred_cap, pred, input, len,
                                 &v)) {
        r.learned = kWalkFailKind;
        return r;
      }
      dir = v ? 1 : 0;
    }
    note_rsan(cur, n, &r);
    uint32_t next = __atomic_load_n(&shm_nodes(shm)[cur].child[dir],
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
    const ShmNode &sn = shm_nodes(shm)[ref];
    const uint32_t c0 =
        __atomic_load_n(&shm_nodes(shm)[ref].child[0], __ATOMIC_ACQUIRE);
    const uint32_t c1 =
        __atomic_load_n(&shm_nodes(shm)[ref].child[1], __ATOMIC_ACQUIRE);
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
  uint32_t cur = __atomic_load_n(&shm_nodes(shm)[sedbt::kRoot].child[0],
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
  if (frontier == sedbt::kRoot) {
    return check_input(shm, input, len);
  }
  if (frontier < sedbt::kRoot || frontier >= shm->hdr.node_cap) return r;
  const ShmNode &fn = shm_nodes(shm)[frontier];
  r.skip_cnt = skip_for(fn, dir);
  uint32_t next =
      __atomic_load_n(&shm_nodes(shm)[frontier].child[dir], __ATOMIC_ACQUIRE);
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
int eval_dir(const SedbtShm *shm, uint32_t cur, const uint8_t *input,
             uint32_t len) {
  if (cur < sedbt::kRoot || cur >= shm->hdr.node_cap) return -1;
  const ShmNode &n = shm_nodes(shm)[cur];
  if (n.unstable) return -1;
  if (n.pred_opaque) return -2;
  if (n.pred_tautology) return n.pred_fixed_dir ? 1 : 0;
  sedbt::Predicate pred;
  pred.root = n.pred_root;
  pred.opaque = 0;
  pred.tautology = 0;
  pred.fixed_dir = n.pred_fixed_dir;
  uint64_t v = 0;
  if (!sedbt::eval_predicate(shm_preds(shm), shm->hdr.pred_cap, pred, input, len,
                             &v))
    return -1;
  return v ? 1 : 0;
}

uint32_t first_child(const SedbtShm *shm, uint32_t frontier, uint8_t dir) {
  if (frontier == sedbt::kRoot) {
    return __atomic_load_n(&shm_nodes(shm)[sedbt::kRoot].child[0],
                           __ATOMIC_ACQUIRE);
  }
  if (frontier < sedbt::kRoot || frontier >= shm->hdr.node_cap || dir > 1)
    return sedbt::kUnexplored;
  return __atomic_load_n(&shm_nodes(shm)[frontier].child[dir], __ATOMIC_ACQUIRE);
}

}  // namespace

static SuffixCmp suffix_walk_uncached(const SedbtShm *shm, uint32_t frontier,
                                      uint8_t dir, const uint8_t *parent,
                                      uint32_t plen, const uint8_t *mut,
                                      uint32_t mlen, SuffixWalkStats *stats) {
  uint32_t cur = first_child(shm, frontier, dir);
  if (cur == sedbt::kTerminal) return SuffixCmp::Same;
  if (cur == sedbt::kUnexplored) return SuffixCmp::Uncertain;
  const uint32_t node_cap = shm->hdr.node_cap;
  uint32_t steps = 0;
  while (true) {
    if (steps++ >= node_cap) return SuffixCmp::Uncertain;
    if (cur < sedbt::kRoot || cur >= node_cap) return SuffixCmp::Uncertain;
    int dp = eval_dir(shm, cur, parent, plen);
    int dm = eval_dir(shm, cur, mut, mlen);
    if (stats) {
      stats->steps += 1;
      stats->evals += 2;
    }
    if (dp < 0 || dm < 0) return SuffixCmp::Uncertain;
    if (dp != dm) {
      uint32_t taken =
          __atomic_load_n(&shm_nodes(shm)[cur].child[(uint8_t)dm],
                          __ATOMIC_ACQUIRE);
      if (taken == sedbt::kUnexplored) return SuffixCmp::Unexplored;
      return SuffixCmp::Explored;
    }
    uint32_t next = __atomic_load_n(&shm_nodes(shm)[cur].child[(uint8_t)dp],
                                    __ATOMIC_ACQUIRE);
    if (next == sedbt::kTerminal) return SuffixCmp::Same;
    if (next == sedbt::kUnexplored) return SuffixCmp::Unexplored;
    cur = next;
  }
}

bool try_lock_path_s_refresh(SedbtShm *shm) {
  if (!shm) return false;
  uint32_t exp = 0;
  return shm->hdr.path_s_refresh_lock.compare_exchange_strong(
      exp, 1u, std::memory_order_acquire, std::memory_order_relaxed);
}

void unlock_path_s_refresh(SedbtShm *shm) {
  if (!shm) return;
  shm->hdr.path_s_refresh_lock.store(0, std::memory_order_release);
}

bool reserve_s_offs(SedbtShm *shm, uint32_t n, uint32_t *out_off) {
  if (!shm || !out_off || n == 0) return false;
  uint32_t s_n = shm->hdr.n_s.load(std::memory_order_relaxed);
  for (;;) {
    if ((uint64_t)s_n + n > shm->hdr.s_cap) return false;
    if (shm->hdr.n_s.compare_exchange_weak(s_n, s_n + n,
                                           std::memory_order_relaxed,
                                           std::memory_order_relaxed)) {
      *out_off = s_n;
      return true;
    }
  }
}

static void collect_node_offsets(const SedbtShm *shm, uint32_t node,
                                 std::unordered_set<uint32_t> *cons,
                                 std::unordered_set<uint32_t> *all) {
  const uint32_t pred_cap = shm->hdr.pred_cap;
  const ShmNode &n = shm_nodes(shm)[node];
  if (n.pred_opaque || n.pred_tautology) return;
  std::vector<uint32_t> one;
  sedbt::collect_input_offsets(shm_preds(shm), pred_cap, n.pred_root, &one);
  for (uint32_t o : one) {
    if (sedbt::is_cons_san_kind(n.constraint)) cons->insert(o);
    all->insert(o);
  }
}

int refresh_suffix_path_s(SedbtShm *shm, uint32_t tail, uint8_t tdir) {
  if (!shm || tdir > 1 || tail < sedbt::kRoot) return 0;
  if (shm->hdr.path_s_mode != (uint8_t)sedbt::PathSMode::Suffix) return 0;
  const uint32_t node_cap = shm->hdr.node_cap;
  if (tail >= node_cap) return 0;
  ShmNode &sn = shm_nodes(shm)[tail];
  uint32_t frontier = sn.term_front[tdir];
  uint8_t fdir = sn.term_fdir[tdir];
  (void)fdir;
  if (frontier < sedbt::kRoot) return 0;
  if (!try_lock_path_s_refresh(shm)) return -1;

  std::unordered_set<uint32_t> cons_set, all_set;
  uint32_t cur = tail;
  uint8_t taken = tdir;
  uint32_t steps = 0;
  while (cur >= sedbt::kRoot && cur < node_cap && steps++ < node_cap) {
    if (cur == frontier) break;
    const ShmNode &n = shm_nodes(shm)[cur];
    uint32_t sib = __atomic_load_n(&shm_nodes(shm)[cur].child[taken ^ 1],
                                   __ATOMIC_ACQUIRE);
    if (sib == sedbt::kUnexplored)
      collect_node_offsets(shm, cur, &cons_set, &all_set);
    uint32_t p = n.parent;
    if (p < sedbt::kRoot || p == cur || p >= node_cap) break;
    uint32_t c0 = __atomic_load_n(&shm_nodes(shm)[p].child[0], __ATOMIC_ACQUIRE);
    uint32_t c1 = __atomic_load_n(&shm_nodes(shm)[p].child[1], __ATOMIC_ACQUIRE);
    if (c0 == cur) taken = 0;
    else if (c1 == cur) taken = 1;
    else break;
    cur = p;
  }

  std::vector<uint32_t> cons(cons_set.begin(), cons_set.end());
  std::vector<uint32_t> rest;
  rest.reserve(all_set.size());
  for (uint32_t o : all_set) {
    if (!cons_set.count(o)) rest.push_back(o);
  }
  std::sort(cons.begin(), cons.end());
  std::sort(rest.begin(), rest.end());
  if (cons.size() > 0xffff) cons.resize(0xffff);
  {
    const uint32_t room = 0xffff - (uint32_t)cons.size();
    if (rest.size() > room) rest.resize(room);
  }
  const uint32_t write_n = (uint32_t)cons.size() + (uint32_t)rest.size();
  const uint32_t old_off =
      __atomic_load_n(&sn.term_s_off[tdir], __ATOMIC_ACQUIRE);
  const uint16_t old_n = sn.term_s_n[tdir];
  const uint16_t old_cons = sn.term_cons_n[tdir];
  int changed = 0;
  if (write_n == old_n && old_cons == (uint16_t)cons.size()) {
    const uint32_t *oldp = shm_s_offs(shm) + old_off;
    bool same = old_off + old_n <= shm->hdr.s_cap;
    for (uint32_t i = 0; same && i < cons.size(); ++i)
      if (oldp[i] != cons[i]) same = false;
    for (uint32_t i = 0; same && i < rest.size(); ++i)
      if (oldp[cons.size() + i] != rest[i]) same = false;
    if (same) {
      unlock_path_s_refresh(shm);
      return 0;
    }
  }
  if (write_n == 0) {
    sn.term_s_n[tdir] = 0;
    sn.term_cons_n[tdir] = 0;
    __atomic_store_n(&sn.term_s_off[tdir], 0, __ATOMIC_RELEASE);
    unlock_path_s_refresh(shm);
    return (old_n != 0) ? 1 : 0;
  }
  uint32_t s_n = 0;
  if (!reserve_s_offs(shm, write_n, &s_n)) {
    unlock_path_s_refresh(shm);
    return -1;
  }
  for (uint32_t i = 0; i < cons.size(); ++i) shm_s_offs(shm)[s_n + i] = cons[i];
  for (uint32_t i = 0; i < rest.size(); ++i)
    shm_s_offs(shm)[s_n + (uint32_t)cons.size() + i] = rest[i];
  sn.term_cons_n[tdir] = (uint16_t)cons.size();
  sn.term_s_n[tdir] = (uint16_t)write_n;
  __atomic_store_n(&sn.term_s_off[tdir], s_n, __ATOMIC_RELEASE);
  changed = 1;
  unlock_path_s_refresh(shm);
  return changed;
}

SuffixCmp suffix_vs_parent(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                           const uint8_t *parent, uint32_t plen,
                           const uint8_t *mut, uint32_t mlen,
                           SuffixWalkStats *stats) {
  if (!shm || !parent || !mut || dir > 1) return SuffixCmp::Uncertain;
  return suffix_walk_uncached(shm, frontier, dir, parent, plen, mut, mlen,
                              stats);
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

void *create_tree_shm(uint64_t bytes, int *fd_out) {
  if (bytes < 4096) return nullptr;
  int fd = memfd_create("symafl-tree", MFD_CLOEXEC);
  if (fd < 0) return nullptr;
  if (ftruncate(fd, (off_t)bytes)) {
    close(fd);
    return nullptr;
  }
  int flags = MAP_SHARED;
#ifdef MAP_NORESERVE
  flags |= MAP_NORESERVE;
#endif
  void *p = mmap(nullptr, (size_t)bytes, PROT_READ | PROT_WRITE, flags, fd, 0);
  if (p == MAP_FAILED) {
    close(fd);
    return nullptr;
  }
  if (fd_out) *fd_out = fd;
  return p;
}

void *map_tree_fd(int fd, uint64_t bytes) {
  if (fd < 0 || bytes < 4096) return nullptr;
  int flags = MAP_SHARED;
#ifdef MAP_NORESERVE
  flags |= MAP_NORESERVE;
#endif
  void *p = mmap(nullptr, (size_t)bytes, PROT_READ | PROT_WRITE, flags, fd, 0);
  return p == MAP_FAILED ? nullptr : p;
}

bool send_fd(int sock, int fd) {
  if (sock < 0 || fd < 0) return false;
  char dummy = 0;
  iovec iov{&dummy, 1};
  char cmsgbuf[CMSG_SPACE(sizeof(int))];
  memset(cmsgbuf, 0, sizeof(cmsgbuf));
  msghdr msg{};
  msg.msg_iov = &iov;
  msg.msg_iovlen = 1;
  msg.msg_control = cmsgbuf;
  msg.msg_controllen = sizeof(cmsgbuf);
  cmsghdr *c = CMSG_FIRSTHDR(&msg);
  c->cmsg_level = SOL_SOCKET;
  c->cmsg_type = SCM_RIGHTS;
  c->cmsg_len = CMSG_LEN(sizeof(int));
  memcpy(CMSG_DATA(c), &fd, sizeof(int));
  return sendmsg(sock, &msg, MSG_NOSIGNAL) > 0;
}

int recv_fd(int sock) {
  if (sock < 0) return -1;
  char dummy = 0;
  iovec iov{&dummy, 1};
  char cmsgbuf[CMSG_SPACE(sizeof(int))];
  memset(cmsgbuf, 0, sizeof(cmsgbuf));
  msghdr msg{};
  msg.msg_iov = &iov;
  msg.msg_iovlen = 1;
  msg.msg_control = cmsgbuf;
  msg.msg_controllen = sizeof(cmsgbuf);
  if (recvmsg(sock, &msg, 0) <= 0) return -1;
  cmsghdr *c = CMSG_FIRSTHDR(&msg);
  if (!c || c->cmsg_level != SOL_SOCKET || c->cmsg_type != SCM_RIGHTS)
    return -1;
  int fd = -1;
  memcpy(&fd, CMSG_DATA(c), sizeof(int));
  return fd;
}

}  // namespace symafl
