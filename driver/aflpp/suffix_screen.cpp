#include "suffix_screen.hpp"

#include "sedbt.hpp"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

namespace symafl {
namespace {

struct TabHdr {
  uint32_t n;
  uint32_t plen;
};
struct TabEnt {
  uint32_t node;
  uint8_t parent_dir;
  uint8_t _pad[3];  // keep TabEnt 8-byte aligned; no semantic field
};
static_assert(sizeof(TabHdr) == 8 && sizeof(TabEnt) == 8,
              "suffix-screen table packing");

struct ScreenStats {
  uint64_t bind = 0, full = 0, spine = 0, trivial = 0, bytes = 0;
  uint32_t spine_log = 0, bind_log = 0;
} g_scr;

struct SuffixStep {
  uint32_t node;
  uint8_t parent_dir;
};

thread_local sedbt::EvalContext g_eval_ctx;

void suffix_eval_reset() { g_eval_ctx.Reset(); }

int suffix_eval_dir(const SedbtShm *shm, uint32_t node, const uint8_t *mut,
                    uint32_t plen) {
  if (!shm || !mut) return -1;
  if (node < sedbt::kRoot || node >= shm->hdr.node_cap) return -1;
  const ShmNode &n = shm_nodes(shm)[node];
  if (n.unstable) return -1;
  if (n.pred_opaque) return -2;
  if (n.pred_tautology) return n.pred_fixed_dir ? 1 : 0;
  sedbt::Predicate pred;
  pred.root = n.pred_root;
  uint64_t v = 0;
  if (!sedbt::eval_predicate(shm_preds(shm), shm->hdr.pred_cap, pred, mut, plen,
                             &v, &g_eval_ctx))
    return -1;
  return v ? 1 : 0;
}

uint32_t tab_install(SedbtShm *shm, const uint8_t *bytes, size_t n) {
  if (!shm || !bytes || n == 0) return 0;
  uint32_t used = shm->hdr.n_tab.load(std::memory_order_relaxed);
  if (used < kTabReserve) used = kTabReserve;
  used = (used + 7u) & ~7u;
  if ((uint64_t)used + n > shm->hdr.tab_cap) {
    g_scr.full += 1;
    if (g_scr.full <= 8)
      fprintf(stderr, "[sedbt-screen] full used=%u need=%zu cap=%u\n", used, n,
              shm->hdr.tab_cap);
    return 0;
  }
  memcpy(shm_tab(shm) + used, bytes, n);
  shm->hdr.n_tab.store(used + (uint32_t)n, std::memory_order_release);
  g_scr.bytes += n;
  return used;
}

uint32_t suffix_screen_admit(SedbtShm *shm) {
  const uint32_t hdr[2] = {0, 0};  // n=0 → suffix_screen admits
  uint32_t off = tab_install(shm, (const uint8_t *)hdr, sizeof(hdr));
  if (off) g_scr.trivial += 1;
  return off;
}

uint32_t emit_table(SedbtShm *shm, const std::vector<SuffixStep> &steps,
                    uint32_t plen) {
  const uint32_t n = (uint32_t)steps.size();
  std::vector<uint8_t> buf(sizeof(TabHdr) + sizeof(TabEnt) * (size_t)n);
  TabHdr h{n, plen};
  memcpy(buf.data(), &h, sizeof(h));
  auto *e = (TabEnt *)(buf.data() + sizeof(TabHdr));
  for (uint32_t i = 0; i < n; ++i) {
    e[i].node = steps[i].node;
    e[i].parent_dir = steps[i].parent_dir;
    e[i]._pad[0] = e[i]._pad[1] = e[i]._pad[2] = 0;
  }
  uint32_t off = tab_install(shm, buf.data(), buf.size());
  if (off) {
    g_scr.bind += 1;
    if (g_scr.bind_log < 8) {
      g_scr.bind_log += 1;
      fprintf(stderr, "[sedbt-screen] bind steps=%u bytes=%zu plen=%u\n", n,
              buf.size(), plen);
    }
  }
  return off;
}

}  // namespace

void suffix_screen_dump_stats() {
  fprintf(stderr,
          "[sedbt-screen] bind=%llu spine=%llu full=%llu trivial=%llu "
          "bytes=%llu cap=%u\n",
          (unsigned long long)g_scr.bind, (unsigned long long)g_scr.spine,
          (unsigned long long)g_scr.full, (unsigned long long)g_scr.trivial,
          (unsigned long long)g_scr.bytes, kTabCap);
}

uint32_t suffix_screen_bind(SedbtShm *shm, uint32_t first, uint32_t n_nodes,
                            uint32_t parent_len) {
  if (!shm || first < sedbt::kRoot || first >= n_nodes) return 0;

  std::vector<SuffixStep> steps;
  uint32_t cur = first;
  bool spine_ok = false;
  for (uint32_t n = 0; n < n_nodes; ++n) {
    if (cur < sedbt::kRoot || cur >= n_nodes) break;
    const ShmNode &sn = shm_nodes(shm)[cur];
    const uint32_t c0 = sn.child[0], c1 = sn.child[1];
    uint8_t pd = 0xff;
    uint32_t next = sedbt::kUnexplored;
    if (c0 != sedbt::kUnexplored && c1 == sedbt::kUnexplored) {
      pd = 0;
      next = c0;
    } else if (c1 != sedbt::kUnexplored && c0 == sedbt::kUnexplored) {
      pd = 1;
      next = c1;
    } else {
      g_scr.spine += 1;
      if (g_scr.spine_log < 8) {
        g_scr.spine_log += 1;
        fprintf(stderr,
                "[sedbt-screen] spine first=%u cur=%u c0=%u c1=%u steps=%zu\n",
                first, cur, c0, c1, steps.size());
      }
      return suffix_screen_admit(shm);
    }
    steps.push_back({cur, pd});
    if (next == sedbt::kTerminal) {
      spine_ok = true;
      break;
    }
    cur = next;
  }
  if (!spine_ok || steps.empty()) {
    g_scr.spine += 1;
    return suffix_screen_admit(shm);
  }
  return emit_table(shm, steps, parent_len);
}

int suffix_screen(const SedbtShm *shm, uint32_t frontier, uint8_t dir,
                  const uint8_t *mut) {
  if (!shm || !mut || dir > 1) return -1;
  const uint32_t node_cap = shm->hdr.node_cap;
  uint32_t first;
  if (frontier == sedbt::kRoot) {
    first = __atomic_load_n(&shm_nodes(shm)[sedbt::kRoot].child[0],
                            __ATOMIC_ACQUIRE);
  } else {
    if (frontier < sedbt::kRoot || frontier >= node_cap) return -1;
    first = __atomic_load_n(&shm_nodes(shm)[frontier].child[dir],
                            __ATOMIC_ACQUIRE);
  }
  if (first == sedbt::kTerminal) return 0;
  if (first == sedbt::kUnexplored) return 1;
  if (first < sedbt::kRoot || first >= node_cap) return -1;
  const uint32_t off = shm_nodes(shm)[first].tab_off;
  if (!off || off + sizeof(TabHdr) > shm->hdr.tab_cap) return -1;
  TabHdr hdr;
  memcpy(&hdr, shm_tab(shm) + off, sizeof(hdr));
  if (hdr.n == 0) return 1;
  if ((uint64_t)off + sizeof(TabHdr) + sizeof(TabEnt) * (uint64_t)hdr.n >
      shm->hdr.tab_cap)
    return -1;
  const auto *ent = (const TabEnt *)(shm_tab(shm) + off + sizeof(TabHdr));
  suffix_eval_reset();
  for (uint32_t i = 0; i < hdr.n; ++i) {
    if (ent[i].node < sedbt::kRoot || ent[i].node >= node_cap) return 1;
    const int d = suffix_eval_dir(shm, ent[i].node, mut, hdr.plen);
    if (d < 0) return 1;
    if ((uint8_t)d != ent[i].parent_dir) {
      const uint32_t taken = __atomic_load_n(
          &shm_nodes(shm)[ent[i].node].child[(uint8_t)d & 1], __ATOMIC_ACQUIRE);
      return taken == sedbt::kUnexplored ? 1 : 0;
    }
  }
  return 0;
}

}  // namespace symafl
