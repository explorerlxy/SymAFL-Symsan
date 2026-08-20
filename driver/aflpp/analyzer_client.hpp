#pragma once

#include "analyzer_ipc.hpp"
#include "shm_sedbt.hpp"

struct AnalyzerClient {
  int sock = -1;
  symafl::SedbtShm *tree = nullptr;
  symafl::FuzzerRing *ring = nullptr;
  symafl::CandArena *cand = nullptr;
  char cand_name[symafl::kNameMax]{};
  uint32_t fuzzer_id = 0;
  uint64_t next_job = 1;
  bool ready = false;
};

bool analyzer_connect(AnalyzerClient *c, const char *sock_path);
bool analyzer_wait_tree_ready(AnalyzerClient *c);
bool analyzer_ack(AnalyzerClient *c);
bool analyzer_wait_done(AnalyzerClient *c);
bool analyzer_submit(AnalyzerClient *c, uint32_t frontier, uint8_t dir,
                   uint32_t skip_cnt, const uint8_t *buf, uint32_t len);
symafl::WalkResult analyzer_check(AnalyzerClient *c, const uint8_t *buf,
                                uint32_t len);
symafl::WalkResult analyzer_check_suffix(AnalyzerClient *c, const uint8_t *buf,
                                         uint32_t len, uint32_t frontier,
                                         uint8_t dir);
bool analyzer_close_bug_edge(AnalyzerClient *c, uint32_t node, uint8_t dir);
void analyzer_close(AnalyzerClient *c);
