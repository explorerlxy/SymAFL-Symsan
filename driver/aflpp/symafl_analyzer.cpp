// symafl-analyzer: ADR 0010. Owns SEDBT + concolic exec. --fuzzers N (default 1).
#include "sedbt.hpp"
#include "shm_sedbt.hpp"
#include "analyzer_ipc.hpp"
#include "suffix_screen.hpp"

#include "dfsan/dfsan.h"

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using namespace symafl;
using namespace __dfsan;

static volatile sig_atomic_t g_stop;
static void on_stop(int) { g_stop = 1; }

// Analyzer fork/exec is not the 48GiB mutator union table. Toy/W1 fits in 256MiB.
static const size_t kWorkerUnionBytes = 256ull << 20;

static bool send_all(int fd, const void *p, size_t n) {
  const uint8_t *b = (const uint8_t *)p;
  size_t off = 0;
  while (off < n) {
    ssize_t w = send(fd, b + off, n - off, MSG_NOSIGNAL);
    if (w <= 0) return false;
    off += (size_t)w;
  }
  return true;
}

static bool recv_all(int fd, void *p, size_t n) {
  uint8_t *b = (uint8_t *)p;
  size_t off = 0;
  while (off < n) {
    ssize_t r = recv(fd, b + off, n - off, 0);
    if (r <= 0) return false;
    off += (size_t)r;
  }
  return true;
}

static bool send_msg(int fd, uint32_t type, uint32_t nbytes, const void *body) {
  CtrlHdr h{type, nbytes};
  if (!send_all(fd, &h, sizeof(h))) return false;
  if (nbytes && body) return send_all(fd, body, nbytes);
  return true;
}

static bool decode_full_stream(const uint8_t *wire, size_t wire_size,
                               std::vector<sedbt::Event> *events) {
  size_t offset = 0;
  while (offset < wire_size) {
    if (wire_size - offset < sizeof(pipe_msg)) return false;
    pipe_msg msg;
    memcpy(&msg, wire + offset, sizeof(msg));
    offset += sizeof(msg);
    if (msg.msg_type == cond_type) {
      if (msg.label == 0 || msg.label == kInitializingLabel) continue;
      uint8_t cons = 0;
      if (msg.flags & F_CONSTRAINT) {
        cons = sedbt::kConstraintPin;
        if (msg.flags & F_GEP_PIN) {
          cons = sedbt::kConstraintGep;
        } else if (msg.flags & F_MEMLEN_PIN) {
          cons = sedbt::kConstraintMemlen;
        } else if (wire_size - offset >= sizeof(pipe_msg)) {
          // Old Fastgen runtimes (build16 dual) emit GEP pins as
          // F_CONSTRAINT only; the GEP metadata record follows immediately.
          pipe_msg nxt;
          memcpy(&nxt, wire + offset, sizeof(nxt));
          if (nxt.msg_type == gep_type) cons = sedbt::kConstraintGep;
        }
      }
      events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0), cons, 1,
                         (uint8_t)((msg.flags & F_RSAN_CHECK)
                                       ? ((msg.flags & F_RSAN_BUG_DIR) ? 1 : 0)
                                       : 0xff)});
      continue;
    }
    if (msg.msg_type == fold_type) {
      if (msg.count < 2 || msg.count > SYMAFL_MAX_FOLD_COUNT) return false;
      if (msg.label == 0 || msg.label == kInitializingLabel) continue;
      events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0), 0,
                         (uint16_t)msg.count});
      continue;
    }
    size_t trailer = 0;
    if (msg.msg_type == gep_type) trailer = sizeof(gep_msg);
    else if (msg.msg_type == memcmp_type && msg.flags)
      trailer = sizeof(memcmp_msg) + (size_t)msg.result;
    else if (msg.msg_type == gv_type) trailer = (size_t)msg.result;
    if (trailer > wire_size - offset) return false;
    offset += trailer;
  }
  return true;
}

static std::vector<std::string> list_seeds(const char *dir) {
  std::vector<std::string> out;
  DIR *d = opendir(dir);
  if (!d) return out;
  while (dirent *e = readdir(d)) {
    if (e->d_name[0] == '.') continue;
    std::string p = std::string(dir) + "/" + e->d_name;
    struct stat st {};
    if (stat(p.c_str(), &st) == 0 && S_ISREG(st.st_mode)) out.push_back(p);
  }
  closedir(d);
  return out;
}

static bool read_file(const char *path, std::vector<uint8_t> *buf) {
  FILE *f = fopen(path, "rb");
  if (!f) return false;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  if (n < 0) {
    fclose(f);
    return false;
  }
  rewind(f);
  buf->resize((size_t)n);
  bool ok = n == 0 || fread(buf->data(), 1, (size_t)n, f) == (size_t)n;
  fclose(f);
  return ok;
}

struct Concolic {
  char union_name[64]{};
  int union_fd = -1;
  dfsan_label_info *labels = nullptr;
  char cur_path[256]{};
};

static bool concolic_init(Concolic *c) {
  snprintf(c->union_name, sizeof(c->union_name), "/symafl-wunion-%d", getpid());
  snprintf(c->cur_path, sizeof(c->cur_path),
           "/home/hahafish/symafl2-work/symafl-analyzer-%d.cur", getpid());
  shm_unlink(c->union_name);
  c->union_fd = shm_open(c->union_name, O_RDWR | O_CREAT | O_EXCL, 0600);
  if (c->union_fd < 0) return false;
  if (ftruncate(c->union_fd, (off_t)kWorkerUnionBytes)) return false;
  c->labels = (dfsan_label_info *)mmap(nullptr, kWorkerUnionBytes, PROT_READ,
                                       MAP_SHARED, c->union_fd, 0);
  return c->labels != MAP_FAILED;
}

static int remaining_ms(const struct timespec &t0, uint32_t timeout_ms) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  int64_t elapsed = (now.tv_sec - t0.tv_sec) * 1000 +
                    (now.tv_nsec - t0.tv_nsec) / 1000000;
  int64_t left = (int64_t)timeout_ms - elapsed;
  if (left < 0) return 0;
  if (left > INT32_MAX) return INT32_MAX;
  return (int)left;
}

// timeout_ms=0 → 30s (bootstrap InsertTrace). Magma concolic execs are
// 1000x+ slower than their cov twins (DFSan on openssl/sndfile parses;
// ssl_ext's static-key handshakes ~5-10s), so 5s killed every slow target's
// bootstrap. Kill the process group on deadline so a hung concolic child
// cannot stall every fuzzer's LearnJob ring.
static bool run_concolic(Concolic *c, const char *bin, const uint8_t *buf,
                         uint32_t len, uint32_t skip, uint32_t timeout_ms,
                         std::vector<sedbt::Event> *events) {
  if (!timeout_ms) timeout_ms = 30000;
  FILE *tf = fopen(c->cur_path, "wb");
  if (!tf) return false;
  if (len && fwrite(buf, 1, len, tf) != len) {
    fclose(tf);
    return false;
  }
  fclose(tf);
  int pipefd[2];
  if (pipe(pipefd)) return false;
  pid_t pid = fork();
  if (pid < 0) {
    close(pipefd[0]);
    close(pipefd[1]);
    return false;
  }
  if (pid == 0) {
    close(pipefd[0]);
    setpgid(0, 0);
    char opt[1024];
    snprintf(opt, sizeof(opt),
             "taint_file=%s:taint_max_len=65536:exit_on_memerror=false:"
             "shm_name=%s:shm_size=%zu:pipe_fd=%d:trace_skip_depth=%u",
             c->cur_path, c->union_name, kWorkerUnionBytes, pipefd[1], skip);
    setenv("TAINT_OPTIONS", opt, 1);
    unsetenv("__AFL_SHM_ID");
    unsetenv("AFL_MAP_SIZE");
    execl(bin, bin, c->cur_path, (char *)nullptr);
    _exit(127);
  }
  setpgid(pid, pid);
  close(pipefd[1]);
  struct timespec t0;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  std::vector<uint8_t> wire;
  uint8_t tmp[4096];
  bool timed_out = false;
  while (true) {
    int left = remaining_ms(t0, timeout_ms);
    if (left == 0) {
      timed_out = true;
      break;
    }
    pollfd pfd{};
    pfd.fd = pipefd[0];
    pfd.events = POLLIN;
    int pr = poll(&pfd, 1, left);
    if (pr < 0) {
      if (errno == EINTR) continue;
      break;
    }
    if (pr == 0) {
      timed_out = true;
      break;
    }
    ssize_t n = read(pipefd[0], tmp, sizeof(tmp));
    if (n > 0) wire.insert(wire.end(), tmp, tmp + n);
    else break;
  }
  close(pipefd[0]);
  if (timed_out) {
    kill(-pid, SIGKILL);
    kill(pid, SIGKILL);
  }
  int st = 0;
  waitpid(pid, &st, 0);
  events->clear();
  if (timed_out) {
    fprintf(stderr, "[analyzer] concolic timeout %ums\n", timeout_ms);
    return false;
  }
  bool ok = decode_full_stream(wire.data(), wire.size(), events);
  if (!ok) {
    fprintf(stderr,
            "[analyzer] concolic stream fail st=0x%x sig=%d wire=%zu\n", st,
            WIFSIGNALED(st) ? WTERMSIG(st) : 0, wire.size());
  }
  return ok;
}

int main(int argc, char **argv) {
  const char *sock_path = nullptr;
  const char *seeds = nullptr;
  const char *concolic = nullptr;
  uint32_t n_fuzzers = 1;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--sock") && i + 1 < argc) sock_path = argv[++i];
    else if (!strcmp(argv[i], "--seeds") && i + 1 < argc) seeds = argv[++i];
    else if (!strcmp(argv[i], "--concolic") && i + 1 < argc)
      concolic = argv[++i];
    else if (!strcmp(argv[i], "--fuzzers") && i + 1 < argc)
      n_fuzzers = (uint32_t)atoi(argv[++i]);
  }
  if (!sock_path || !seeds || !concolic || n_fuzzers < 1 ||
      n_fuzzers > kMaxFuzzers) {
    fprintf(stderr,
            "usage: symafl-analyzer --sock PATH --seeds DIR --concolic BIN "
            "[--fuzzers N]\n");
    return 2;
  }

  uint64_t tree_bytes = kTreeMapBytes;
  int tfd = -1;
  auto *tree_shm = (SedbtShm *)create_tree_shm(tree_bytes, &tfd);
  if (!tree_shm) {
    tree_bytes = 64ull << 30;
    tree_shm = (SedbtShm *)create_tree_shm(tree_bytes, &tfd);
  }
  if (!tree_shm) {
    tree_bytes = 8ull << 30;
    tree_shm = (SedbtShm *)create_tree_shm(tree_bytes, &tfd);
  }
  if (!tree_shm) {
    fprintf(stderr, "[analyzer] tree shm create failed\n");
    return 1;
  }
  memset(tree_shm, 0, 4096);
  if (!sedbt_layout(&tree_shm->hdr, tree_bytes)) {
    fprintf(stderr, "[analyzer] tree layout failed bytes=%llu\n",
            (unsigned long long)tree_bytes);
    return 1;
  }
  tree_shm->hdr.magic = kIpcMagic;
  tree_shm->hdr.version = kIpcVersion;
  fprintf(stderr,
          "[analyzer] tree map=%lluB nodes=%u preds=%u tab=%u (lazy pages)\n",
          (unsigned long long)tree_bytes, tree_shm->hdr.node_cap,
          tree_shm->hdr.pred_cap, tree_shm->hdr.tab_cap);

  sedbt::Tree tree(nullptr);
  tree.attach(tree_shm);
  tree.apply_mut_compute_env();
  fprintf(stderr, "[analyzer] compute path_s=%s closure=%s "
          "(off: CONS_SAN root→terminal, no explore symbols; "
          "suffix: suffix CONS_SAN+symbols, screen on; "
          "full: CONS_SAN+symbols root→terminal, screen off)\n",
          sedbt::path_s_mode_name(tree.path_s_mode()),
          tree.compute_closures() ? "on" : "off");

  unlink(sock_path);
  int ls = socket(AF_UNIX, SOCK_STREAM, 0);
  sockaddr_un addr{};
  addr.sun_family = AF_UNIX;
  snprintf(addr.sun_path, sizeof(addr.sun_path), "%s", sock_path);
  if (bind(ls, (sockaddr *)&addr, sizeof(addr)) ||
      listen(ls, (int)n_fuzzers)) {
    perror("bind/listen");
    return 1;
  }
  fprintf(stderr, "[analyzer] listen %s fuzzers=%u\n", sock_path, n_fuzzers);

  struct Client {
    int sock = -1;
    uint32_t id = 0;
    FuzzerRing *ring = nullptr;
    CandArena *cand = nullptr;
    char ring_name[kNameMax]{};
    bool acked = false;
  };
  std::vector<Client> clients(n_fuzzers);
  for (uint32_t i = 0; i < n_fuzzers; ++i) {
    int fsock = accept(ls, nullptr, nullptr);
    if (fsock < 0) {
      perror("accept");
      return 1;
    }
    CtrlHdr h{};
    if (!recv_all(fsock, &h, sizeof(h)) || h.type != kHello) return 1;
    HelloBody hello{};
    if (h.nbytes != sizeof(hello) || !recv_all(fsock, &hello, sizeof(hello)))
      return 1;
    Client &c = clients[i];
    c.sock = fsock;
    c.id = i;
    int cfd = -1, rfd = -1;
    c.cand = (CandArena *)open_shm(hello.cand_name, sizeof(CandArena), &cfd);
    snprintf(c.ring_name, sizeof(c.ring_name), "/symafl-ring-%d-%u", getpid(),
             i);
    c.ring = (FuzzerRing *)create_shm(c.ring_name, sizeof(FuzzerRing), &rfd);
    if (!c.cand || !c.ring) {
      fprintf(stderr, "[analyzer] map ring/cand failed id=%u cand=%s\n", i,
              hello.cand_name);
      return 1;
    }
    HelloOkBody ok{};
    ok.fuzzer_id = i;
    ok.tree_bytes = tree_bytes;
    snprintf(ok.tree_name, sizeof(ok.tree_name), "%s", "memfd");
    snprintf(ok.ring_name, sizeof(ok.ring_name), "%s", c.ring_name);
    if (!send_msg(fsock, kHelloOk, sizeof(ok), &ok)) return 1;
    if (!send_fd(fsock, tfd)) {
      fprintf(stderr, "[analyzer] send tree fd failed id=%u\n", i);
      return 1;
    }
    fprintf(stderr, "[analyzer] hello id=%u cand=%s ring=%s\n", i, hello.cand_name,
            c.ring_name);
  }

  Concolic co{};
  if (!concolic_init(&co)) {
    fprintf(stderr, "[analyzer] concolic shm failed\n");
    return 1;
  }
  const size_t max_label = kWorkerUnionBytes / sizeof(dfsan_label_info);
  for (const std::string &sp : list_seeds(seeds)) {
    std::vector<uint8_t> buf;
    if (!read_file(sp.c_str(), &buf)) continue;
    std::vector<sedbt::Event> ev;
    if (!run_concolic(&co, concolic, buf.data(), (uint32_t)buf.size(), 0, 0,
                      &ev)) {
      fprintf(stderr, "[analyzer] concolic fail %s\n", sp.c_str());
      continue;
    }
    sedbt::NodeRef tail = sedbt::kUnexplored;
    uint8_t tdir = 0;
    tree.InsertTrace(ev, co.labels, max_label, buf.data(),
                     (uint32_t)buf.size(), &tail, &tdir);
    fprintf(stderr, "[analyzer] bootstrap %s events=%zu nodes=%u\n", sp.c_str(),
            ev.size(), tree.live_nodes());
  }
  for (auto &c : clients) {
    if (!send_msg(c.sock, kTreeReady, 0, nullptr)) return 1;
  }

  uint32_t n_ack = 0;
  while (n_ack < n_fuzzers) {
    std::vector<pollfd> pfds(n_fuzzers);
    for (uint32_t i = 0; i < n_fuzzers; ++i) {
      pfds[i].fd = clients[i].acked ? -1 : clients[i].sock;
      pfds[i].events = POLLIN;
      pfds[i].revents = 0;
    }
    if (poll(pfds.data(), n_fuzzers, -1) < 0) {
      perror("poll ack");
      return 1;
    }
    for (uint32_t i = 0; i < n_fuzzers; ++i) {
      if (clients[i].acked || !(pfds[i].revents & POLLIN)) continue;
      CtrlHdr h{};
      if (!recv_all(clients[i].sock, &h, sizeof(h)) ||
          h.type != kBootstrapAck) {
        fprintf(stderr, "[analyzer] ACK failed id=%u\n", i);
        return 1;
      }
      if (h.nbytes) {
        std::string junk(h.nbytes, '\0');
        recv_all(clients[i].sock, junk.data(), h.nbytes);
      }
      clients[i].acked = true;
      n_ack++;
      fprintf(stderr, "[analyzer] ack id=%u (%u/%u)\n", i, n_ack, n_fuzzers);
    }
  }
  for (auto &c : clients) {
    if (!send_msg(c.sock, kBootstrapDone, 0, nullptr)) return 1;
    fcntl(c.sock, F_SETFL, O_NONBLOCK);
  }
  fprintf(stderr, "[analyzer] BOOTSTRAP_DONE; polling\n");

  signal(SIGINT, on_stop);
  signal(SIGTERM, on_stop);

  uint32_t rr = 0;
  uint32_t jobs[kMaxFuzzers] = {};
  for (;;) {
    if (g_stop) break;
    uint32_t alive = 0;
    for (auto &c : clients) {
      if (c.sock < 0) continue;
      CtrlHdr ch{};
      ssize_t n = recv(c.sock, &ch, sizeof(ch), MSG_DONTWAIT);
      if (n < 0) {
        alive++;
        continue;
      }
      if (n == 0 || (n == (ssize_t)sizeof(ch) && ch.type == kShutdown)) {
        close(c.sock);
        c.sock = -1;
        continue;
      }
      if (n == (ssize_t)sizeof(ch) && ch.nbytes) {
        std::string junk(ch.nbytes, '\0');
        recv_all(c.sock, junk.data(), ch.nbytes);
      }
      alive++;
    }
    if (!alive) break;

    bool did = false;
    for (uint32_t k = 0; k < n_fuzzers; ++k) {
      uint32_t i = (rr + k) % n_fuzzers;
      Client &c = clients[i];
      if (!c.ring) continue;
      uint64_t head = c.ring->head.v.load(std::memory_order_relaxed);
      uint64_t tail = c.ring->tail.v.load(std::memory_order_acquire);
      if (head == tail) continue;
      LearnJob job = c.ring->slots[head % kRingCap];
      rr = i + 1;
      did = true;
      fprintf(stderr, "[analyzer] job fuzzer=%u kind=%u frontier=%u dir=%u\n", i,
              job.kind, job.frontier, job.dir);
      if (job.kind == kJobCloseBug) {
        if (tree.CloseUnexplored((sedbt::NodeRef)job.frontier, job.dir)) {
          fprintf(stderr, "[analyzer] close-bug node=%u dir=%u\n", job.frontier,
                  job.dir);
        }
        c.ring->head.v.store(head + 1, std::memory_order_release);
        jobs[i] += 1;
        break;
      }
      uint32_t clen =
          c.cand->slots[job.cand_idx].len.load(std::memory_order_acquire);
      if (clen == 0 || clen > kCandMax) {
        fprintf(stderr, "[analyzer] drop bad cand fuzzer=%u clen=%u\n", i,
                clen);
        c.ring->head.v.store(head + 1, std::memory_order_release);
        jobs[i] += 1;
        break;
      }
      // Hold head until this LearnJob is done so the fuzzer cannot reuse
      // cand[idx] / ring[idx]. Read the slot in place (no private copy).
      const uint8_t *cbuf = c.cand->slots[job.cand_idx].bytes;
      auto hit = tree.CheckSuffix((sedbt::NodeRef)job.frontier, job.dir, cbuf,
                                  clen);
      if (hit.kind != sedbt::Tree::SuffixKind::Frontier) {
        fprintf(stderr, "[analyzer] drop fuzzer=%u frontier=%u dir=%u kind=%u\n",
                i, job.frontier, job.dir, (unsigned)hit.kind);
        c.ring->head.v.store(head + 1, std::memory_order_release);
        jobs[i] += 1;
        break;
      }
      if (hit.frontier != job.frontier || hit.dir != job.dir) {
        fprintf(stderr,
                "[analyzer] retarget fuzzer=%u %u/%u -> %u/%u skip=%u\n", i,
                job.frontier, job.dir, hit.frontier, hit.dir, hit.skip_cnt);
      }
      std::vector<sedbt::Event> ev;
      if (!run_concolic(&co, concolic, cbuf, clen, hit.skip_cnt, job.timeout_ms,
                        &ev)) {
        fprintf(stderr,
                "[analyzer] concolic fail fuzzer=%u frontier=%u (slot held)\n",
                i, job.frontier);
        break;
      }
      sedbt::NodeRef path_tail = sedbt::kUnexplored;
      uint8_t tdir = 0;
      // Path-s binds at hit.(frontier,dir), which may be deeper than
      // job.(frontier,dir). The closed edge stores that bind site
      // (term_front/term_fdir) so the fuzzer's later CheckSuffix-to-terminal
      // can adopt it; the LearnJob fields themselves are not rewritten.
      tree.InsertSuffix(hit.frontier, hit.dir, ev, co.labels, max_label, cbuf,
                        clen, &path_tail, &tdir);
      c.ring->head.v.store(head + 1, std::memory_order_release);
      jobs[i] += 1;
      fprintf(stderr,
              "[analyzer] suffix fuzzer=%u frontier=%u dir=%u events=%zu "
              "nodes=%u\n",
              i, hit.frontier, hit.dir, ev.size(), tree.live_nodes());
      break;
    }
    if (!did) __builtin_ia32_pause();
  }
  for (uint32_t i = 0; i < n_fuzzers; ++i)
    fprintf(stderr, "[analyzer] jobs fuzzer=%u n=%u\n", i, jobs[i]);
  if (const char *dump = getenv("SYMAFL_TREE_DUMP")) {
    tree.Dump(dump);
    fprintf(stderr, "[analyzer] tree dump -> %s nodes=%u\n", dump,
            tree.live_nodes());
  }
  symafl::suffix_screen_dump_stats();
  return 0;
}
