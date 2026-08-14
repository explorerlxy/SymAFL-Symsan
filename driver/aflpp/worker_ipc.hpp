// ADR 0010 IPC: control socket messages, LearnJob ring, candidate SHM, live SEDBT.
#pragma once

#include <atomic>
#include <cstdint>
#include <vector>

#include "pcbt.hpp"

namespace symafl {

constexpr uint32_t kIpcMagic = 0x53313031u;  // S101
constexpr uint32_t kIpcVersion = 2;
constexpr uint32_t kRingCap = 256;
constexpr uint32_t kCandSlots = kRingCap;
constexpr uint32_t kCandMax = 65536;
constexpr uint32_t kNodeCap = 1u << 18;
constexpr uint32_t kPredCap = 1u << 20;
constexpr uint32_t kSCap = 1u << 20;
constexpr uint32_t kECap = 1u << 18;
constexpr uint32_t kNameMax = 64;
constexpr uint32_t kMaxFuzzers = 16;

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
  uint32_t fuzzer_id;  // hint; worker assigns 0..N-1
  char cand_name[kNameMax];
};

struct HelloOkBody {
  uint32_t fuzzer_id;
  char tree_name[kNameMax];
  char ring_name[kNameMax];
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
  AtomicU64 head;  // worker advances
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

// Flattened SEDBT node. child[] published with release after the node is init.
struct ShmNode {
  uint32_t cid;
  uint32_t pred_root;
  uint32_t child[2];
  uint32_t depth;
  uint32_t skipCnt;
  uint32_t parent;
  uint32_t s_off;
  uint32_t e_off;
  uint16_t s_n;
  uint16_t e_n;
  uint8_t rCnt[2];
  uint8_t pred_opaque;
  uint8_t pred_tautology;
  uint8_t pred_fixed_dir;
  uint8_t constraint;
  uint8_t unstable;
  uint8_t len_related;
  uint8_t rsan_bug_dir;  // 0xff = not RSan (W3)
  uint8_t trigger_neg;
  uint8_t closure_present;
  uint8_t _pad;
};

struct SedbtHeader {
  uint32_t magic;
  uint32_t version;
  std::atomic<uint32_t> n_nodes;
  std::atomic<uint32_t> n_preds;
  std::atomic<uint32_t> n_s;
  std::atomic<uint32_t> n_e;
  uint32_t node_cap;
  uint32_t pred_cap;
  uint32_t s_cap;
  uint32_t e_cap;
};

struct SedbtShm {
  SedbtHeader hdr;
  ShmNode nodes[kNodeCap];
  pcbt::PNode preds[kPredCap];
  uint32_t s_offs[kSCap];
  ShmClause e_clauses[kECap];
};

enum Learned : uint8_t { kUnlearned = 0, kLearned = 1, kWalkFail = 2 };

struct WalkResult {
  uint8_t learned;  // Learned
  uint32_t frontier;
  uint8_t dir;
  uint32_t skip_cnt;
  std::vector<pcbt::AttachedClosure> closures;
};

}  // namespace symafl
