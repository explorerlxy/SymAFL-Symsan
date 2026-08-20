// ADR 0010 IPC: control socket messages, LearnJob ring, candidate SHM, live SEDBT.
#pragma once

#include <atomic>
#include <cstdint>
#include <vector>

#include "pred.hpp"

namespace symafl {

constexpr uint32_t kIpcMagic = 0x53313031u;  // S101
constexpr uint32_t kIpcVersion = 7;
constexpr uint32_t kRingCap = 256;
constexpr uint32_t kCandSlots = kRingCap;
constexpr uint32_t kCandMax = 65536;
constexpr uint32_t kNodeCap = 1u << 18;
constexpr uint32_t kPredCap = 1u << 20;
constexpr uint32_t kSCap = 1u << 20;
constexpr uint32_t kECap = 1u << 18;
constexpr uint32_t kClosCap = 1u << 16;
constexpr uint32_t kNameMax = 64;
constexpr uint32_t kMaxFuzzers = 16;

enum CtrlType : uint32_t {
  kHello = 1,
  kHelloOk = 2,
  kTreeReady = 3,
  kBootstrapAck = 4,
  kBootstrapDone = 5,
  kShutdown = 6,
  kCloseBugEdge = 7,  // fuzzer → analyzer: mark RSan bug child terminal
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
  char tree_name[kNameMax];
  char ring_name[kNameMax];
};

struct CloseBugBody {
  uint32_t node;
  uint8_t dir;
  uint8_t _pad[3];
};

struct LearnJob {
  uint64_t job_id;
  uint32_t fuzzer_id;
  uint32_t cand_idx;
  uint32_t frontier;
  uint32_t skip_cnt;
  uint8_t dir;
  uint8_t _pad[3];
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
  uint16_t term_cons_n[2];  // prefix of term_s_*[dir] from GEP-index pins
  uint8_t term_fdir[2];
  uint8_t pred_opaque;
  uint8_t pred_tautology;
  uint8_t pred_fixed_dir;
  uint8_t constraint;  // 0 ordinary, 1 pin, 2 GEP-index pin
  uint8_t unstable;
  uint8_t len_related;
  uint8_t rsan_bug_dir;  // 0xff = not RSan
};

struct SedbtHeader {
  uint32_t magic;
  uint32_t version;
  std::atomic<uint32_t> n_nodes;
  std::atomic<uint32_t> n_preds;
  std::atomic<uint32_t> n_s;
  std::atomic<uint32_t> n_e;
  std::atomic<uint32_t> n_clos;
  uint32_t node_cap;
  uint32_t pred_cap;
  uint32_t s_cap;
  uint32_t e_cap;
  uint32_t clos_cap;
  uint8_t path_s_mode;  // sedbt::PathSMode
  uint8_t _pad_mode[3];
};

struct SedbtShm {
  SedbtHeader hdr;
  ShmNode nodes[kNodeCap];
  sedbt::PNode preds[kPredCap];
  uint32_t s_offs[kSCap];
  ShmClause e_clauses[kECap];
  ShmClosure clos[kClosCap];
};

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
