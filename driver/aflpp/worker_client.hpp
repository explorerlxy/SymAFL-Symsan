#pragma once

#include "worker_ipc.hpp"
#include "shm_sedbt.hpp"

#include <string>
#include <unordered_map>

struct WorkerClient {
  int sock = -1;
  symafl::SedbtShm *tree = nullptr;
  symafl::FuzzerRing *ring = nullptr;
  symafl::CandArena *cand = nullptr;
  char cand_name[symafl::kNameMax]{};
  uint32_t fuzzer_id = 0;
  uint64_t next_job = 1;
  std::unordered_map<std::string, uint8_t> learned;
  bool ready = false;
};

bool worker_connect(WorkerClient *c, const char *sock_path);
bool worker_wait_tree_ready(WorkerClient *c);
bool worker_ack(WorkerClient *c);
bool worker_wait_done(WorkerClient *c);
bool worker_submit(WorkerClient *c, uint32_t frontier, uint8_t dir,
                   uint32_t skip_cnt, const uint8_t *buf, uint32_t len);
symafl::WalkResult worker_check(WorkerClient *c, const uint8_t *buf,
                                uint32_t len);
void worker_close(WorkerClient *c);
