#include "analyzer_client.hpp"

#include <errno.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include <cstdio>
#include <cstring>
#include <string>

namespace {

bool send_all(int fd, const void *p, size_t n) {
  const uint8_t *b = (const uint8_t *)p;
  size_t off = 0;
  while (off < n) {
    ssize_t w = send(fd, b + off, n - off, MSG_NOSIGNAL);
    if (w <= 0) return false;
    off += (size_t)w;
  }
  return true;
}

bool recv_all(int fd, void *p, size_t n) {
  uint8_t *b = (uint8_t *)p;
  size_t off = 0;
  while (off < n) {
    ssize_t r = recv(fd, b + off, n - off, 0);
    if (r <= 0) return false;
    off += (size_t)r;
  }
  return true;
}

bool send_hdr(int fd, uint32_t type, uint32_t nbytes, const void *body) {
  symafl::CtrlHdr h{type, nbytes};
  if (!send_all(fd, &h, sizeof(h))) return false;
  if (nbytes && body) return send_all(fd, body, nbytes);
  return true;
}

bool recv_hdr(int fd, symafl::CtrlHdr *h) {
  return recv_all(fd, h, sizeof(*h));
}

}  // namespace

bool analyzer_connect(AnalyzerClient *c, const char *sock_path) {
  snprintf(c->cand_name, sizeof(c->cand_name), "/symafl-cand-%d", getpid());
  int cfd = -1;
  c->cand = (symafl::CandArena *)symafl::create_shm(
      c->cand_name, sizeof(symafl::CandArena), &cfd);
  if (!c->cand) return false;

  c->sock = socket(AF_UNIX, SOCK_STREAM, 0);
  if (c->sock < 0) return false;
  sockaddr_un addr{};
  addr.sun_family = AF_UNIX;
  snprintf(addr.sun_path, sizeof(addr.sun_path), "%s", sock_path);
  if (connect(c->sock, (sockaddr *)&addr, sizeof(addr))) {
    close(c->sock);
    c->sock = -1;
    return false;
  }
  symafl::HelloBody hello{};
  hello.fuzzer_id = 0;
  snprintf(hello.cand_name, sizeof(hello.cand_name), "%s", c->cand_name);
  if (!send_hdr(c->sock, symafl::kHello, sizeof(hello), &hello)) return false;
  symafl::CtrlHdr h{};
  if (!recv_hdr(c->sock, &h) || h.type != symafl::kHelloOk ||
      h.nbytes != sizeof(symafl::HelloOkBody))
    return false;
  symafl::HelloOkBody ok{};
  if (!recv_all(c->sock, &ok, sizeof(ok))) return false;
  c->fuzzer_id = ok.fuzzer_id;
  int tfd = symafl::recv_fd(c->sock);
  c->tree = (symafl::SedbtShm *)symafl::map_tree_fd(tfd, ok.tree_bytes);
  if (tfd >= 0) close(tfd);
  int rfd = -1;
  c->ring = (symafl::FuzzerRing *)symafl::open_shm(ok.ring_name,
                                                  sizeof(symafl::FuzzerRing),
                                                  &rfd);
  fprintf(stderr, "[sedbt] analyzer hello-ok id=%u tree=%s ring=%s cand=%s\n",
          c->fuzzer_id, ok.tree_name, ok.ring_name, c->cand_name);
  if (!c->tree || !c->ring || !c->cand) return false;
  if (c->tree->hdr.magic != symafl::kIpcMagic ||
      c->tree->hdr.version != symafl::kIpcVersion) {
    fprintf(stderr,
            "[sedbt] SEDBT SHM layout mismatch magic=0x%x version=%u "
            "(want 0x%x / %u); rebuild analyzer and mutator together\n",
            c->tree->hdr.magic, c->tree->hdr.version, symafl::kIpcMagic,
            symafl::kIpcVersion);
    return false;
  }
  return true;
}

bool analyzer_wait_tree_ready(AnalyzerClient *c) {
  if (!c || c->sock < 0) return false;
  symafl::CtrlHdr h{};
  if (!recv_hdr(c->sock, &h)) return false;
  if (h.nbytes) {
    std::string junk(h.nbytes, '\0');
    if (!recv_all(c->sock, junk.data(), h.nbytes)) return false;
  }
  c->ready = (h.type == symafl::kTreeReady);
  return c->ready;
}

bool analyzer_ack(AnalyzerClient *c) {
  return c && send_hdr(c->sock, symafl::kBootstrapAck, 0, nullptr);
}

bool analyzer_wait_done(AnalyzerClient *c) {
  symafl::CtrlHdr h{};
  if (!recv_hdr(c->sock, &h)) return false;
  if (h.nbytes) {
    std::string junk(h.nbytes, '\0');
    recv_all(c->sock, junk.data(), h.nbytes);
  }
  return h.type == symafl::kBootstrapDone;
}

bool analyzer_submit(AnalyzerClient *c, uint32_t frontier, uint8_t dir,
                   uint32_t skip_cnt, const uint8_t *buf, uint32_t len,
                   uint32_t timeout_ms, uint8_t kind) {
  if (!c || !c->ring || !c->cand) return false;
  if (kind == symafl::kJobLearn &&
      (!buf || len == 0 || len > symafl::kCandMax))
    return false;
  uint64_t head = c->ring->head.v.load(std::memory_order_acquire);
  uint64_t tail = c->ring->tail.v.load(std::memory_order_relaxed);
  if (tail - head >= symafl::kRingCap) return false;
  uint32_t idx = (uint32_t)(tail % symafl::kRingCap);
  if (kind == symafl::kJobLearn) {
    memcpy(c->cand->slots[idx].bytes, buf, len);
    c->cand->slots[idx].len.store(len, std::memory_order_release);
  } else {
    c->cand->slots[idx].len.store(0, std::memory_order_release);
  }
  symafl::LearnJob job{};
  job.job_id = c->next_job++;
  job.fuzzer_id = c->fuzzer_id;
  job.cand_idx = idx;
  job.frontier = frontier;
  job.skip_cnt = skip_cnt;
  job.timeout_ms = timeout_ms;
  job.dir = dir;
  job.kind = kind;
  c->ring->slots[idx] = job;
  c->ring->tail.v.store(tail + 1, std::memory_order_release);
  return true;
}

bool analyzer_submit_close(AnalyzerClient *c, uint32_t node, uint8_t dir) {
  return analyzer_submit(c, node, dir, 0, nullptr, 0, 0, symafl::kJobCloseBug);
}

symafl::WalkResult analyzer_check(AnalyzerClient *c, const uint8_t *buf,
                                uint32_t len) {
  if (!c || !c->tree) {
    symafl::WalkResult r{};
    r.learned = symafl::kWalkFailKind;
    return r;
  }
  return symafl::check_input(c->tree, buf, len);
}

symafl::WalkResult analyzer_check_suffix(AnalyzerClient *c, const uint8_t *buf,
                                         uint32_t len, uint32_t frontier,
                                         uint8_t dir) {
  if (!c || !c->tree) {
    symafl::WalkResult r{};
    r.learned = symafl::kWalkFailKind;
    return r;
  }
  return symafl::check_suffix(c->tree, buf, len, frontier, dir);
}

void analyzer_close(AnalyzerClient *c) {
  if (!c) return;
  if (c->sock >= 0) {
    close(c->sock);
    c->sock = -1;
  }
  if (c->cand_name[0]) {
    shm_unlink(c->cand_name);
    c->cand_name[0] = 0;
  }
}
