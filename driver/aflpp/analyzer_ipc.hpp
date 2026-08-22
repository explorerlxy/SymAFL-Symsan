// ADR 0010 IPC: control socket messages, LearnJob ring, candidate SHM, live SEDBT.
#pragma once

#include <atomic>
#include <cstdint>
#include <vector>

#include "pred.hpp"

namespace symafl {

constexpr uint32_t kIpcMagic = 0x53313031u;  // S101
constexpr uint32_t kIpcVersion = 15;
constexpr uint32_t kRingCap = 256;
constexpr uint32_t kCandSlots = kRingCap;
constexpr uint32_t kCandMax = 65536;
// Production tree is a 1TiB virtual map (memfd, lazy physical pages). Caps
// are the maximum that layout will take from that map; tests pack smaller.
constexpr uint64_t kTreeMapBytes = 1ull << 40;
constexpr uint32_t kNodeCap = 1u << 27;   // ~134M nodes
constexpr uint32_t kPredCap = 1u << 27;
constexpr uint32_t kSCap = 1u << 26;
constexpr uint32_t kECap = 1u << 25;
constexpr uint32_t kClosCap = 1u << 22;
constexpr uint32_t kTabCap = 1u << 30;  // 1GiB suffix-screen tables
constexpr uint32_t kTabReserve = 8;
constexpr uint32_t kNameMax = 64;
constexpr uint32_t kMaxFuzzers = 16;
constexpr uint64_t kLocalTreeBytes = 32ull << 20;  // in-process Tree() / tests

enum CtrlType : uint32_t {
  kHello = 1,
  kHelloOk = 2,
  kTreeReady = 3,
  kBootstrapAck = 4,
  kBootstrapDone = 5,
  kShutdown = 6,
};

struct CtrlHdr {
  uint32_t type;
  uint32_t nbytes;
};

struct HelloBody {
  uint32_t fuzzer_id;  // hint; analyzer assigns 0..N-1
  char cand_name[kNameMax];
};

struct HelloOkBody {
  uint32_t fuzzer_id;
  uint32_t _pad;
  uint64_t tree_bytes;  // mmap size of the tree memfd
  char tree_name[kNameMax];  // "memfd"
  char ring_name[kNameMax];
};

enum JobKind : uint8_t {
  kJobLearn = 0,     // CheckSuffix + concolic + InsertSuffix
  kJobCloseBug = 1,  // no concolic: CloseUnexplored(frontier, dir)
};

struct LearnJob {
  uint64_t job_id;
  uint32_t fuzzer_id;
  uint32_t cand_idx;
  uint32_t frontier;
  uint32_t skip_cnt;
  uint32_t timeout_ms;  // 50 × queue seed exec_us; 0 → analyzer default
  uint8_t dir;
  uint8_t kind;  // JobKind
  uint8_t _pad[2];
};

struct alignas(64) AtomicU64 {
  std::atomic<uint64_t> v;
};

struct FuzzerRing {
  AtomicU64 head;  // analyzer advances
  char _pad_head[64 - sizeof(AtomicU64)];
  AtomicU64 tail;  // fuzzer advances
  char _pad_tail[64 - sizeof(AtomicU64)];
  LearnJob slots[kRingCap];
};

struct CandSlot {
  std::atomic<uint32_t> len;
  uint8_t bytes[kCandMax];
};

struct CandArena {
  CandSlot slots[kCandSlots];
};

struct ShmClause {
  uint32_t pred_root;
  uint8_t negated;
  uint8_t _pad[3];
};

// RSan closure payload. Only allocated slots exist; ShmNode.clos_i is 0 or
// 1-based index into this table. Ordinary nodes do not carry s/e.
struct ShmClosure {
  uint32_t s_off;
  uint32_t e_off;
  uint16_t s_n;
  uint16_t e_n;
  uint8_t trigger_neg;
  uint8_t _pad[3];
};

// Topology + flags only. Path-s for a closed terminal edge is term_s_*[dir]
// (O(1) at CheckInput). Closures live in `clos[]`, not here.
// term_front/term_fdir is the InsertSuffix (retargeted) bind site for that
// closed edge: 0 = unset; kRoot is 2. CheckSuffix-to-terminal copies these
// into WalkResult so the fuzzer's SeedLearn path-s matches the insert edge,
// not the submit-time LearnJob frontier.
struct ShmNode {
  uint32_t cid;
  uint32_t pred_root;
  uint32_t child[2];
  uint32_t depth;
  uint32_t skipCnt;
  uint32_t parent;
  uint32_t clos_i;  // 0 = none; else 1-based ShmClosure index
  uint32_t term_s_off[2];
  uint32_t term_front[2];
  uint16_t term_s_n[2];
  uint16_t term_cons_n[2];  // prefix of term_s_*[dir] from CONS_SAN pins
  uint8_t term_fdir[2];
  uint8_t pred_opaque;
  uint8_t pred_tautology;
  uint8_t pred_fixed_dir;
  uint8_t constraint;  // 0 ordinary, 1 pin, 2 GEP, 3 copy-size
  uint8_t unstable;
  uint8_t len_related;
  uint8_t rsan_bug_dir;  // 0xff = not RSan
  uint32_t tab_off;      // 0 = none; else byte offset of suffix-screen table
};

struct SedbtHeader {
  uint32_t magic;
  uint32_t version;
  std::atomic<uint32_t> n_nodes;
  std::atomic<uint32_t> n_preds;
  std::atomic<uint32_t> n_s;
  std::atomic<uint32_t> n_e;
  std::atomic<uint32_t> n_clos;
  std::atomic<uint32_t> n_tab;
  uint32_t node_cap;
  uint32_t pred_cap;
  uint32_t s_cap;
  uint32_t e_cap;
  uint32_t clos_cap;
  uint32_t tab_cap;
  uint64_t map_bytes;
  uint64_t node_off;
  uint64_t pred_off;
  uint64_t s_off;
  uint64_t e_off;
  uint64_t clos_off;
  uint64_t tab_off;
  uint8_t path_s_mode;  // sedbt::PathSMode
  uint8_t _pad_mode[3];
  // Writers only: fuzzers rebinding suffix path-s. Readers of term_s_* do
  // not take this. 0 = free, 1 = held.
  std::atomic<uint32_t> path_s_refresh_lock;
};

// Mapping is hdr.map_bytes (1TiB in production). Regions sit at *_off.
struct SedbtShm {
  SedbtHeader hdr;
};

inline uint64_t sedbt_align_page(uint64_t x) { return (x + 4095ull) & ~4095ull; }

inline bool sedbt_layout(SedbtHeader *h, uint64_t map_bytes) {
  if (!h || map_bytes < (1u << 20)) return false;
  auto need = [](uint32_t n, uint32_t pc, uint32_t sc, uint32_t ec, uint32_t cc,
                 uint32_t tc) -> uint64_t {
    uint64_t off = sedbt_align_page(sizeof(SedbtHeader));
    off = sedbt_align_page(off + (uint64_t)n * sizeof(ShmNode));
    off = sedbt_align_page(off + (uint64_t)pc * sizeof(sedbt::PNode));
    off = sedbt_align_page(off + (uint64_t)sc * sizeof(uint32_t));
    off = sedbt_align_page(off + (uint64_t)ec * sizeof(ShmClause));
    off = sedbt_align_page(off + (uint64_t)cc * sizeof(ShmClosure));
    off = sedbt_align_page(off + (uint64_t)tc);
    return off;
  };
  uint32_t n = kNodeCap, pc = kPredCap, sc = kSCap, ec = kECap, cc = kClosCap,
           tc = kTabCap;
  while (n > 16 && need(n, pc, sc, ec, cc, tc) > map_bytes) {
    n /= 2;
    if (pc > 16) pc /= 2;
    if (sc > 16) sc /= 2;
    if (ec > 16) ec /= 2;
    if (cc > 16) cc /= 2;
    if (tc > 4096) tc /= 2;
  }
  if (need(n, pc, sc, ec, cc, tc) > map_bytes) return false;
  uint64_t off = sedbt_align_page(sizeof(SedbtHeader));
  h->node_off = off;
  h->node_cap = n;
  off = sedbt_align_page(off + (uint64_t)n * sizeof(ShmNode));
  h->pred_off = off;
  h->pred_cap = pc;
  off = sedbt_align_page(off + (uint64_t)pc * sizeof(sedbt::PNode));
  h->s_off = off;
  h->s_cap = sc;
  off = sedbt_align_page(off + (uint64_t)sc * sizeof(uint32_t));
  h->e_off = off;
  h->e_cap = ec;
  off = sedbt_align_page(off + (uint64_t)ec * sizeof(ShmClause));
  h->clos_off = off;
  h->clos_cap = cc;
  off = sedbt_align_page(off + (uint64_t)cc * sizeof(ShmClosure));
  h->tab_off = off;
  h->tab_cap = tc;
  h->map_bytes = map_bytes;
  (void)off;
  return true;
}

inline ShmNode *shm_nodes(SedbtShm *s) {
  return reinterpret_cast<ShmNode *>(reinterpret_cast<char *>(s) +
                                     s->hdr.node_off);
}
inline const ShmNode *shm_nodes(const SedbtShm *s) {
  return reinterpret_cast<const ShmNode *>(reinterpret_cast<const char *>(s) +
                                           s->hdr.node_off);
}
inline sedbt::PNode *shm_preds(SedbtShm *s) {
  return reinterpret_cast<sedbt::PNode *>(reinterpret_cast<char *>(s) +
                                          s->hdr.pred_off);
}
inline const sedbt::PNode *shm_preds(const SedbtShm *s) {
  return reinterpret_cast<const sedbt::PNode *>(
      reinterpret_cast<const char *>(s) + s->hdr.pred_off);
}
inline uint32_t *shm_s_offs(SedbtShm *s) {
  return reinterpret_cast<uint32_t *>(reinterpret_cast<char *>(s) +
                                      s->hdr.s_off);
}
inline const uint32_t *shm_s_offs(const SedbtShm *s) {
  return reinterpret_cast<const uint32_t *>(reinterpret_cast<const char *>(s) +
                                            s->hdr.s_off);
}
inline ShmClause *shm_e_clauses(SedbtShm *s) {
  return reinterpret_cast<ShmClause *>(reinterpret_cast<char *>(s) +
                                       s->hdr.e_off);
}
inline const ShmClause *shm_e_clauses(const SedbtShm *s) {
  return reinterpret_cast<const ShmClause *>(
      reinterpret_cast<const char *>(s) + s->hdr.e_off);
}
inline ShmClosure *shm_clos_tab(SedbtShm *s) {
  return reinterpret_cast<ShmClosure *>(reinterpret_cast<char *>(s) +
                                        s->hdr.clos_off);
}
inline const ShmClosure *shm_clos_tab(const SedbtShm *s) {
  return reinterpret_cast<const ShmClosure *>(
      reinterpret_cast<const char *>(s) + s->hdr.clos_off);
}
inline uint8_t *shm_tab(SedbtShm *s) {
  return reinterpret_cast<uint8_t *>(reinterpret_cast<char *>(s) +
                                     s->hdr.tab_off);
}
inline const uint8_t *shm_tab(const SedbtShm *s) {
  return reinterpret_cast<const uint8_t *>(reinterpret_cast<const char *>(s) +
                                           s->hdr.tab_off);
}

// Seed-level learned (mutator). WalkResult.learned is the walk kind, which
// uses the same numbers for terminal (1) and fail (3); frontier walks are 0
// until the mutator records in-flight (0) vs ring-full (2).
enum Learned : uint8_t {
  kInFlight = 0,  // LearnJob submitted; wait and CheckSuffix
  kReady = 1,     // complete trace; path_s + RSan node refs available
  kRingFull = 2,  // retry submit (or CheckSuffix if frontier closed)
  kWalkFail = 3,  // unstable / eval failure
};

enum WalkKind : uint8_t {
  kWalkFrontier = 0,
  kWalkTerminal = 1,
  kWalkFailKind = 3,
};

struct WalkResult {
  uint8_t learned;  // WalkKind
  uint32_t frontier;
  uint8_t dir;
  uint32_t skip_cnt;
  uint32_t last_node;
  uint8_t last_dir;
  uint32_t path_s_off;
  uint16_t path_s_n;
  uint16_t path_s_cons_n;
  uint8_t path_s_ready;
  std::vector<uint32_t> rsan_nodes;  // RSan node refs on this walk (0-copy)
};

}  // namespace symafl
