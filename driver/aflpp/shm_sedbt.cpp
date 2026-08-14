#include "shm_sedbt.hpp"

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <cstring>
#include <cstdio>

namespace symafl {

void pack_node(const pcbt::Tree &tree, pcbt::NodeRef ref, ShmNode *out) {
  const pcbt::Node &n = tree.node_at(ref);
  out->cid = n.cid;
  out->pred_root = n.pred.root;
  out->child[0] = n.child[0];
  out->child[1] = n.child[1];
  out->depth = n.depth;
  out->skipCnt = n.skipCnt;
  out->parent = n.parent;
  out->rCnt[0] = n.rCnt[0];
  out->rCnt[1] = n.rCnt[1];
  out->pred_opaque = n.pred.opaque ? 1 : 0;
  out->pred_tautology = n.pred.tautology ? 1 : 0;
  out->pred_fixed_dir = n.pred.fixed_dir;
  out->constraint = n.constraint ? 1 : 0;
  out->unstable = n.unstable ? 1 : 0;
  out->len_related = n.len_related ? 1 : 0;
  out->rsan_bug_dir = n.rsan_bug_dir;
  out->trigger_neg = n.closure.trigger_neg;
}

static void publish_one_closure(SedbtShm *shm, const pcbt::Tree &tree,
                                uint32_t ref) {
  const pcbt::Closure &c = tree.closure_of(ref);
  ShmNode &sn = shm->nodes[ref];
  if (!c.present || sn.closure_present) return;
  uint32_t s_n = shm->hdr.n_s.load(std::memory_order_relaxed);
  uint32_t e_n = shm->hdr.n_e.load(std::memory_order_relaxed);
  if (s_n + c.s.size() > shm->hdr.s_cap) return;
  if (e_n + c.e.size() > shm->hdr.e_cap) return;
  sn.s_off = s_n;
  sn.s_n = (uint16_t)c.s.size();
  for (uint32_t i = 0; i < c.s.size(); ++i) shm->s_offs[s_n + i] = c.s[i];
  sn.e_off = e_n;
  sn.e_n = (uint16_t)c.e.size();
  for (uint32_t i = 0; i < c.e.size(); ++i) {
    shm->e_clauses[e_n + i].pred_root = c.e[i].pred_root;
    shm->e_clauses[e_n + i].negated = c.e[i].negated;
  }
  shm->hdr.n_s.store(s_n + (uint32_t)c.s.size(), std::memory_order_release);
  shm->hdr.n_e.store(e_n + (uint32_t)c.e.size(), std::memory_order_release);
  sn.trigger_neg = c.trigger_neg;
  sn.closure_present = 1;
}

void publish_tree(SedbtShm *shm, const pcbt::Tree &tree) {
  const uint32_t old_n = shm->hdr.n_nodes.load(std::memory_order_relaxed);
  const uint32_t old_p = shm->hdr.n_preds.load(std::memory_order_relaxed);
  const uint32_t new_n = tree.live_nodes();
  const uint32_t new_p = tree.live_preds();
  if (new_n > shm->hdr.node_cap || new_p > shm->hdr.pred_cap) return;

  const pcbt::PNode *preds = tree.pred_data();
  if (new_p > old_p)
    memcpy(&shm->preds[old_p], preds + old_p,
           sizeof(pcbt::PNode) * (new_p - old_p));
  shm->hdr.n_preds.store(new_p, std::memory_order_release);

  for (uint32_t i = old_n; i < new_n; ++i) {
    pack_node(tree, i, &shm->nodes[i]);
  }
  shm->hdr.n_nodes.store(new_n, std::memory_order_release);

  for (uint32_t i = pcbt::kRoot; i < new_n; ++i)
    publish_one_closure(shm, tree, i);

  for (uint32_t i = pcbt::kRoot; i < old_n && i < new_n; ++i) {
    const pcbt::Node &n = tree.node_at(i);
    for (int d = 0; d < 2; ++d) {
      uint32_t want = n.child[d];
      uint32_t have = shm->nodes[i].child[d];
      if (want != have)
        __atomic_store_n(&shm->nodes[i].child[d], want, __ATOMIC_RELEASE);
    }
  }
}

static uint32_t skip_for(const ShmNode &parent, uint8_t dir) {
  return parent.skipCnt + (parent.constraint && dir == 1 ? 1 : 0);
}

static void attach_if_bug_open(const SedbtShm *shm, uint32_t cur,
                               const ShmNode &n,
                               std::vector<pcbt::AttachedClosure> *out) {
  if (n.rsan_bug_dir > 1 || !n.closure_present || !out) return;
  uint32_t bug = __atomic_load_n(&shm->nodes[cur].child[n.rsan_bug_dir],
                                 __ATOMIC_ACQUIRE);
  if (bug != pcbt::kUnexplored) return;
  pcbt::AttachedClosure a;
  a.node = cur;
  a.bug_dir = n.rsan_bug_dir;
  a.trigger_neg = n.trigger_neg;
  a.trigger_root = n.pred_root;
  a.s.assign(shm->s_offs + n.s_off, shm->s_offs + n.s_off + n.s_n);
  a.e.reserve(n.e_n);
  for (uint16_t i = 0; i < n.e_n; ++i) {
    const ShmClause &cl = shm->e_clauses[n.e_off + i];
    a.e.push_back({cl.pred_root, cl.negated});
  }
  out->push_back(std::move(a));
}

WalkResult check_input(const SedbtShm *shm, const uint8_t *input,
                       uint32_t len) {
  WalkResult r{};
  r.learned = kWalkFail;
  const uint32_t n_nodes = shm->hdr.n_nodes.load(std::memory_order_acquire);
  const uint32_t n_preds = shm->hdr.n_preds.load(std::memory_order_acquire);
  if (n_nodes <= pcbt::kRoot) {
    r.learned = kUnlearned;
    r.frontier = pcbt::kRoot;
    r.dir = 0;
    r.skip_cnt = 0;
    return r;
  }
  uint32_t cur = __atomic_load_n(&shm->nodes[pcbt::kRoot].child[0],
                                 __ATOMIC_ACQUIRE);
  if (cur == pcbt::kUnexplored) {
    r.learned = kUnlearned;
    r.frontier = pcbt::kRoot;
    r.dir = 0;
    r.skip_cnt = 0;
    return r;
  }
  while (true) {
    if (cur == pcbt::kTerminal) {
      r.learned = kLearned;
      return r;
    }
    if (cur < pcbt::kRoot || cur >= n_nodes) {
      r.learned = kWalkFail;
      return r;
    }
    const ShmNode &n = shm->nodes[cur];
    if (n.unstable) {
      r.learned = kWalkFail;
      return r;
    }
    uint8_t dir = 0;
    if (n.pred_tautology || n.pred_opaque) {
      dir = n.pred_tautology ? n.pred_fixed_dir : 0;
    } else {
      pcbt::Predicate pred;
      pred.root = n.pred_root;
      pred.opaque = n.pred_opaque;
      pred.tautology = n.pred_tautology;
      pred.fixed_dir = n.pred_fixed_dir;
      uint64_t v = 0;
      if (!pcbt::eval_predicate(shm->preds, n_preds, pred, input, len, &v)) {
        r.learned = kWalkFail;
        return r;
      }
      dir = v ? 1 : 0;
    }
    attach_if_bug_open(shm, cur, n, &r.closures);
    uint32_t next = __atomic_load_n(&shm->nodes[cur].child[dir],
                                    __ATOMIC_ACQUIRE);
    if (next == pcbt::kUnexplored) {
      r.learned = kUnlearned;
      r.frontier = cur;
      r.dir = dir;
      r.skip_cnt = skip_for(n, dir);
      return r;
    }
    if (next == pcbt::kTerminal) {
      r.learned = kLearned;
      return r;
    }
    cur = next;
  }
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
