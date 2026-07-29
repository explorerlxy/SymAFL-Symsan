/*
  SymAFL v2 custom mutator for AFL++: PCBT-guided seed screening.

  Based on the SymSan AFL++ driver
  (c) 2023 - 2024 by Chengyu Song <csong@ucr.edu>, Apache 2.0.

  v2 strips the solving chain (no TaskManager / Solver / custom mutations):
  AFL++ does traditional fuzzing only. The mutator
    (1) runs traced re-executions of queue entries (SymSan instrumented
        binary, launched per entry) and inserts their symbolic branch-event
        streams into a PCBT (path-constraint binary trie);
    (2) screens mutated candidates against the PCBT in
        afl_custom_post_process (Phase 2).
*/

#include "dfsan/dfsan.h"

#include "pcbt.hpp"

extern "C" {
#include "afl-fuzz.h"
#include "launch.h"
}

#include <algorithm>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <fcntl.h>

using namespace __dfsan;

#ifndef DEBUG
#define DEBUG 0
#endif

#if !DEBUG
#undef DEBUGF
#define DEBUGF(_str...) do { } while (0)
#endif

#define MIN_TIMEOUT 50U
// traced re-runs can be much slower than fuzz runs (full concolic
// tracing); SYMAFL_TRACE_TIMEOUT_MS overrides the cap (0 = use
// min(MIN_TIMEOUT, exec_tmout)).
static uint32_t TraceTimeoutMs = 0;

static int TraceBounds = 0;
static int ExitOnMemError = 1;  // default is exit on memory error
static int SolveUB = 0;
static int ForceStdin = 0;

#undef alloc_printf
#define alloc_printf(_str...) ({ \
    char* _tmp; \
    s32 _len = snprintf(NULL, 0, _str); \
    if (_len < 0) FATAL("Whoa, snprintf() fails?!"); \
    _tmp = (char*)ck_alloc(_len + 1); \
    snprintf((char*)_tmp, _len + 1, _str); \
    _tmp; \
  })

struct my_mutator_t {
  my_mutator_t() = delete;
  explicit my_mutator_t(const afl_state_t *afl)
      : afl(afl), out_dir(NULL), out_file(NULL), symsan_bin(NULL),
        argv(NULL), out_fd(-1) {}

  ~my_mutator_t() {
    if (out_fd >= 0) close(out_fd);
    ck_free(out_dir);
    ck_free(out_file);
    ck_free(argv);
  }

  const afl_state_t *afl;
  char *out_dir;
  char *out_file;
  char *symsan_bin;
  char **argv;
  int out_fd;

  pcbt::Tree tree;
  std::unordered_set<std::string> traced_entries;
  bool bootstrap_done = false;

  // screening state (post_process)
  bool screening = true;
  uint32_t rlimit = 16;
  pcbt::Node *last_node = nullptr;
  uint8_t last_dir = 0;
  bool last_gained = true;

  // stats
  uint64_t traced_runs = 0;
  uint64_t failed_runs = 0;
  uint64_t trace_timeouts = 0;
  uint64_t memerr_events = 0;
  uint64_t screened = 0;
  uint64_t admitted = 0;
  uint64_t vetoed = 0;
  uint64_t vetoes_since_admit = 0;
  bool saturation_logged = false;
  uint64_t selfcheck_fail = 0;  // inserted input vetoed by its own tree
};

// shared union table (owned by the launcher)
static dfsan_label_info *__dfsan_label_info;
static const size_t MAX_LABEL = uniontable_size / sizeof(dfsan_label_info);

dfsan_label_info *__dfsan::get_label_info(dfsan_label label) {
  if (unlikely(label >= MAX_LABEL)) {
    throw std::out_of_range("label too large " + std::to_string(label));
  }
  return &__dfsan_label_info[label];
}

/// no splice input
extern "C" void afl_custom_splice_optout(my_mutator_t *data) {
  (void)(data);
}

extern "C" my_mutator_t *afl_custom_init(afl_state *afl, unsigned int seed) {
  (void)(seed);

  struct stat st;
  my_mutator_t *data = new my_mutator_t(afl);
  if (!data) {
    FATAL("afl_custom_init alloc");
    return NULL;
  }

  if (getenv("SYMSAN_TRACE_BOUNDS")) {
    TraceBounds = 1;
  }
  if (getenv("SYMSAN_DONT_EXIT_ON_MEMERROR")) {
    ExitOnMemError = 0;
  }
  if (getenv("SYMSAN_SOLVE_UB")) {
    TraceBounds = 1;  // solve undefined depends on trace bounds
    SolveUB = 1;
  }
  if (getenv("SYMSAN_FORCE_STDIN")) {
    ForceStdin = 1;
  }

  if (!(data->symsan_bin = getenv("SYMSAN_TARGET"))) {
    FATAL(
        "SYMSAN_TARGET not defined, this should point to the full path of "
        "the symsan compiled binary.");
  }

  if (!(data->out_dir = getenv("SYMSAN_OUTPUT_DIR"))) {
    data->out_dir = alloc_printf("%s/symsan", afl->out_dir);
  }

  if (stat(data->out_dir, &st) && mkdir(data->out_dir, 0755)) {
    PFATAL("Could not create the output directory %s", data->out_dir);
  }

  // setup output file (input for traced runs)
  char *out_file;
  if (afl->file_extension) {
    out_file = alloc_printf("%s/.cur_input.%s", data->out_dir, afl->file_extension);
  } else {
    out_file = alloc_printf("%s/.cur_input", data->out_dir);
  }
  if (data->out_dir[0] == '/') {
    data->out_file = out_file;
  } else {
    char cwd[PATH_MAX];
    if (getcwd(cwd, (size_t)sizeof(cwd)) == NULL) { PFATAL("getcwd() failed"); }
    data->out_file = alloc_printf("%s/%s", cwd, out_file);
    ck_free(out_file);
  }

  data->out_fd = open(data->out_file, O_RDWR | O_CREAT | O_TRUNC, 0644);
  if (data->out_fd < 0) {
    PFATAL("Failed to create output file %s: %s\n", data->out_file,
           strerror(errno));
  }

  // setup symsan launcher (shared union table)
  __dfsan_label_info = (dfsan_label_info *)symsan_init(data->symsan_bin,
                                                       uniontable_size);
  if (__dfsan_label_info == (void *)-1) {
    FATAL("Failed to init symsan launcher: %s\n", strerror(errno));
  }

  if (getenv("SYMAFL_NO_SCREEN")) {
    data->screening = false;
  }
  if (const char *rl = getenv("SYMAFL_RCNT_LIMIT")) {
    data->rlimit = (uint32_t)atoi(rl);
  }
  if (const char *tto = getenv("SYMAFL_TRACE_TIMEOUT_MS")) {
    TraceTimeoutMs = (uint32_t)atoi(tto);
  }

  return data;
}

extern "C" void afl_custom_deinit(my_mutator_t *data) {
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt] traces=%llu nodes=%llu depth=%llu conflicts=%llu "
          "failed=%llu timeouts=%llu memerr=%llu screened=%llu "
          "admitted=%llu vetoed=%llu saturated=%llu "
          "selfcheck_fail=%llu\n",
          (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
          (unsigned long long)t.max_depth,
          (unsigned long long)t.num_conflicts,
          (unsigned long long)data->failed_runs,
          (unsigned long long)data->trace_timeouts,
          (unsigned long long)data->memerr_events,
          (unsigned long long)data->screened,
          (unsigned long long)data->admitted,
          (unsigned long long)data->vetoed,
          (unsigned long long)(data->screening ? 0 : 1),
          (unsigned long long)data->selfcheck_fail);
  symsan_destroy();
  delete data;
}

// One-time launcher setup (deferred: afl->argv/fsrv are not ready at
// init, and queue_new_entry already fires during pivot_inputs before the
// target argv is parsed). Returns false while afl->argv is unavailable.
static bool setup_launcher_once(my_mutator_t *data) {
  if (likely(data->argv != NULL)) return true;
  if (data->afl->argv == NULL) return false;

  int argc = 0;
  while (data->afl->argv[argc]) { argc++; }
  data->argv = (char **)calloc(argc + 1, sizeof(char *));
  if (!data->argv) {
    FATAL("Failed to alloc argv\n");
  }
  for (int i = 0; i < argc; i++) {
    if (strstr(data->afl->argv[i], (char *)data->afl->tmp_dir)) {
      DEBUGF("Replacing %s with %s\n", data->afl->argv[i], data->out_file);
      data->argv[i] = data->out_file;
    } else {
      data->argv[i] = data->afl->argv[i];
    }
  }
  data->argv[argc] = NULL;
  symsan_set_input(data->afl->fsrv.use_stdin ? "stdin" : data->out_file);
  symsan_set_args(argc, data->argv);
  symsan_set_debug(DEBUG);
  symsan_set_bounds_check(TraceBounds);
  symsan_set_exit_on_memerror(ExitOnMemError);
  symsan_set_solve_ub(SolveUB);
  symsan_set_force_stdin(ForceStdin);
  return true;
}

/// Run one traced execution of `buf` and insert the branch-event stream
/// into the PCBT.
static void trace_and_insert(my_mutator_t *data, const u8 *buf,
                             size_t buf_size, const char *fname) {
  if (!setup_launcher_once(data)) return;

  // write the input for the traced run
  lseek(data->out_fd, 0, SEEK_SET);
  ck_write(data->out_fd, buf, buf_size, data->out_file);
  fsync(data->out_fd);
  if (ftruncate(data->out_fd, buf_size)) {
    WARNF("Failed to truncate output file: %s\n", strerror(errno));
    data->failed_runs += 1;
    return;
  }

  u32 timeout = TraceTimeoutMs ? TraceTimeoutMs
                               : std::min(MIN_TIMEOUT, data->afl->fsrv.exec_tmout);

  struct timeval t0, t1, t2;
  gettimeofday(&t0, NULL);
  FILE *dump = getenv("SYMAFL_TRACE_DUMP")
                   ? fopen(getenv("SYMAFL_TRACE_DUMP"), "a") : nullptr;
  int ret = symsan_run(data->out_fd);
  if (ret < 0) {
    WARNF("Failed to start symsan bin: %s\n", strerror(errno));
    data->failed_runs += 1;
    return;
  } else if (ret > 0) {
    WARNF("symsan_run failed %d\n", ret);
    data->failed_runs += 1;
    return;
  }
  data->traced_runs += 1;

  std::vector<pcbt::Event> events;
  events.reserve(4096);

  pipe_msg msg;
  gep_msg gmsg;
  memcmp_msg *mmsg;
  dfsan_label_info *info;
  size_t msg_size;
  u32 num_msgs = 0;
  bool timedout = false;
  struct timeval start, end;
  gettimeofday(&start, NULL);

  while (symsan_read_event(&msg, sizeof(msg), timeout) == sizeof(msg)) {
    switch (msg.msg_type) {
      case cond_type:
        if (dump) {
          fprintf(dump, "cond cid=%x label=%u r=%llu\n", msg.id, msg.label,
                  (unsigned long long)msg.result);
          fflush(dump);
        }
        if (unlikely(msg.label == 0 || msg.label == kInitializingLabel)) {
          break;  // concrete branch / uninitialized: not a tree node
        }
        events.push_back({msg.id, msg.label, (uint8_t)(msg.result != 0)});
        break;
      case gep_type:
        // symbolic address: consume the trailer, not a tree node (v2)
        if (symsan_read_event(&gmsg, sizeof(gmsg), 0) != sizeof(gmsg)) {
          WARNF("Failed to receive gep msg: %s\n", strerror(errno));
        }
        break;
      case memcmp_type:
        if (msg.label == 0 || msg.label >= MAX_LABEL) break;
        info = get_label_info(msg.label);
        if (info->l1 != CONST_LABEL && info->l2 != CONST_LABEL) break;
        msg_size = sizeof(memcmp_msg) + msg.result;
        mmsg = (memcmp_msg *)malloc(msg_size);
        if (symsan_read_event(mmsg, msg_size, 0) != msg_size) {
          WARNF("Failed to receive memcmp msg: %s\n", strerror(errno));
          free(mmsg);
          break;
        }
        free(mmsg);  // content not needed for the tree (v2)
        break;
      case memerr_type:
        data->memerr_events += 1;
        WARNF("Memory error detected @%p, type = %d\n", (void *)msg.addr,
              msg.flags);
        break;
      default:
        break;
    }
    // naive deadloop detection
    num_msgs += 1;
    if (unlikely((num_msgs & 0xffffe000) != 0)) {
      gettimeofday(&end, NULL);
      if ((end.tv_sec - start.tv_sec) * 10 > timeout) {
        WARNF("Possible deadloop, break\n");
        timedout = true;
        break;
      }
    }
  }

  if (timedout) {
    symsan_terminate();
    data->trace_timeouts += 1;
    return;  // discard truncated traces (v1 replay-mismatch semantics)
  }

  if (dump) fclose(dump);
  gettimeofday(&t1, NULL);
  int xstatus = 0;
  if (symsan_get_exit_status(&xstatus) == 0 &&
      !(WIFEXITED(xstatus) && WEXITSTATUS(xstatus) <= 1)) {
    data->failed_runs += 1;
    WARNF("traced child abnormal exit: status=0x%x (events=%zu)\n", xstatus,
          events.size());
  }

  uint32_t created = data->tree.InsertTrace(events, __dfsan_label_info, MAX_LABEL);
  gettimeofday(&t2, NULL);
  fprintf(stderr,
          "[pcbt-trace] %s events=%zu created=%u read_ms=%ld insert_ms=%ld xstatus=%#x\n",
          fname, events.size(), created,
          (t1.tv_sec - t0.tv_sec) * 1000 + (t1.tv_usec - t0.tv_usec) / 1000,
          (t2.tv_sec - t1.tv_sec) * 1000 + (t2.tv_usec - t1.tv_usec) / 1000,
          xstatus);

  // self-consistency check: the just-inserted input must be admitted by
  // CheckInput (its path now exists and ends at a fresh frontier). A veto
  // here means converter/evaluator semantics diverge from execution.
  {
    pcbt::Node *node = nullptr;
    uint8_t dir = 0;
    if (!data->tree.CheckInput(buf, (uint32_t)buf_size, &node, &dir,
                               data->rlimit)) {
      data->selfcheck_fail += 1;
    }
  }
}

/// Read a queue file and trace+insert it (once per entry).
static void trace_entry_file(my_mutator_t *data, const char *fname) {
  if (data->traced_entries.count(fname)) return;  // already traced
  if (data->afl->argv == NULL) return;  // launcher not ready (pivot_inputs)

  data->traced_entries.insert(fname);
  int fd = open(fname, O_RDONLY);
  if (fd < 0) {
    WARNF("Failed to open queue file %s: %s\n", fname, strerror(errno));
    return;
  }
  struct stat st;
  if (fstat(fd, &st) || st.st_size <= 0 || st.st_size > MAX_FILE) {
    fprintf(stderr, "[pcbt-trace] SKIP %s (fstat/size: %ld)\n", fname,
            st.st_size);
    close(fd);
    return;
  }
  std::vector<u8> buf(st.st_size);
  ssize_t got = read(fd, buf.data(), buf.size());
  close(fd);
  if (got != (ssize_t)buf.size()) {
    fprintf(stderr, "[pcbt-trace] SKIP %s (short read %zd/%zu)\n", fname, got,
            buf.size());
    return;
  }

  trace_and_insert(data, buf.data(), buf.size(), fname);
}

/// Bootstrap: AFL++ v4.31c uses weighted (alias-table) queue selection —
/// slow but coverage-rich entries (exactly the ones that grow the tree)
/// may never be selected, so queue-selection-driven tracing starves.
/// Instead, on the first queue_get (argv is ready by then) we sweep the
/// entire current queue (initial corpus + dry-run finds); entries arriving
/// later are traced by queue_new_entry. Learning is thus coverage-driven,
/// not selection-driven.
extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  (void)(filename);
  if (!data->bootstrap_done && data->afl->argv != NULL) {
    data->bootstrap_done = true;
    for (u32 i = 0; i < data->afl->queued_items; i++) {
      trace_entry_file(data, (const char *)data->afl->queue_buf[i]->fname);
    }
  }
  return 1;  // always allow fuzzing the entry
}

/// Trace every coverage-gaining entry (v1's "gaining replay" analogue).
extern "C" u8 afl_custom_queue_new_entry(my_mutator_t *data,
                                         const u8 *filename_new_queue,
                                         const u8 *filename_orig_queue) {
  (void)(filename_orig_queue);
  data->last_gained = true;  // the last admitted candidate gained coverage
  trace_entry_file(data, (const char *)filename_new_queue);
  return 0;
}

/// PCBT screening: veto mutated candidates that cannot reach an unexplored
/// frontier. Returning 0 with *out_buf=NULL tells AFL++ to skip executing
/// this candidate entirely.
extern "C" size_t afl_custom_post_process(my_mutator_t *data, u8 *buf,
                                          size_t buf_size, u8 **out_buf) {
  // rCnt bookkeeping for the previously admitted candidate
  if (data->last_node) {
    if (!data->last_gained) data->last_node->rCnt[data->last_dir] += 1;
    data->last_node = nullptr;
  }

  if (!data->screening) {
    *out_buf = buf;
    return buf_size;
  }

  data->screened += 1;
  pcbt::Node *node = nullptr;
  uint8_t dir = 0;
  if (data->tree.CheckInput(buf, (uint32_t)buf_size, &node, &dir,
                            data->rlimit)) {
    data->admitted += 1;
    data->vetoes_since_admit = 0;
    if (node) {
      data->last_node = node;
      data->last_dir = dir;
      data->last_gained = false;
    }
    *out_buf = buf;
    return buf_size;
  }

  data->vetoed += 1;
  // saturation watchdog: if the whole reachable frontier is rCnt-pruned,
  // every candidate is vetoed and the fuzzer would stall. After 1M
  // consecutive vetoes fall back to passthrough (plain AFL) and log it.
  if (++data->vetoes_since_admit >= 1000000 && data->screening) {
    data->screening = false;
    if (!data->saturation_logged) {
      data->saturation_logged = true;
      fprintf(stderr,
              "[pcbt] frontier saturated after %llu vetoes, screening off\n",
              (unsigned long long)data->vetoed);
    }
  }
  *out_buf = NULL;
  return 0;
}

extern "C" const char *afl_custom_introspection(my_mutator_t *data) {
  static char buf[512];
  const pcbt::Tree &t = data->tree;
  snprintf(buf, sizeof(buf),
           "traces=%llu nodes=%llu depth=%llu conflicts=%llu "
           "failed=%llu timeouts=%llu memerr=%llu "
           "screened=%llu admitted=%llu vetoed=%llu saturated=%llu "
           "selfcheck_fail=%llu",
           (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
           (unsigned long long)t.max_depth,
           (unsigned long long)t.num_conflicts,
           (unsigned long long)data->failed_runs,
           (unsigned long long)data->trace_timeouts,
           (unsigned long long)data->memerr_events,
           (unsigned long long)data->screened,
           (unsigned long long)data->admitted,
           (unsigned long long)data->vetoed,
           (unsigned long long)(data->screening ? 0 : 1),
           (unsigned long long)data->selfcheck_fail);
  return buf;
}
