/*
  SymAFL v2 custom mutator for AFL++: PCBT-guided seed screening.

  Based on the SymSan AFL++ driver
  (c) 2023 - 2024 by Chengyu Song <csong@ucr.edu>, Apache 2.0.

  v2 strips the solving chain (no TaskManager / Solver / custom mutations):
  AFL++ does traditional fuzzing only. The mutator
    (1) arms the SymSan forkserver target to capture symbolic branch-event
        streams for admitted candidates, then inserts coverage-gaining paths
        into a PCBT (path-constraint binary trie);
    (2) screens mutated candidates against the PCBT in
        afl_custom_post_process (Phase 2).
*/

#include "dfsan/dfsan.h"

#include "pcbt.hpp"

extern "C" {
#include "afl-fuzz.h"
}

#include <algorithm>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include <stdlib.h>
#include <string.h>
#include <time.h>
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

// Bootstrap always uses pipe-full so every initial path enters the tree.
// Steady state uses bounded SHM suffix capture. Pipe suffix is reserved for a
// confirmed coverage-gaining input whose SHM capture overflowed.

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
  explicit my_mutator_t(afl_state_t *afl) : afl(afl) {}

  ~my_mutator_t() {
    if (progress_log) {
      fclose(progress_log);
      progress_log = nullptr;
    }
    if (single_pass_control) {
      munmap(single_pass_control, single_pass_size);
    }
    if (single_pass_label_info) {
      munmap(single_pass_label_info, uniontable_size);
    }
    if (single_pass_trace_fd >= 0) close(single_pass_trace_fd);
    if (single_pass_union_fd >= 0) close(single_pass_union_fd);
    if (single_pass_trace_name) {
      shm_unlink(single_pass_trace_name);
      ck_free(single_pass_trace_name);
    }
    if (single_pass_union_name) {
      shm_unlink(single_pass_union_name);
      ck_free(single_pass_union_name);
    }
    if (full_stream_read_fd >= 0) close(full_stream_read_fd);
    if (full_stream_write_fd >= 0) close(full_stream_write_fd);
  }

  afl_state_t *afl;

  pcbt::Tree tree;
  std::unordered_set<std::string> traced_entries;
  bool bootstrap_done = false;

  // screening state (post_process)
  bool screening = true;
  uint8_t rlimit = 16;
  pcbt::NodeRef last_node = pcbt::kUnexplored;
  uint8_t last_dir = 0;
  bool last_gained = true;

  // Single-pass capture state. The target forkserver maps both regions once;
  // each admitted candidate arms the small control block for its own child.
  char *single_pass_union_name = nullptr;
  char *single_pass_trace_name = nullptr;
  int single_pass_union_fd = -1;
  int single_pass_trace_fd = -1;
  dfsan_label_info *single_pass_label_info = nullptr;
  symafl_single_pass_control *single_pass_control = nullptr;
  size_t single_pass_size = 0;
  bool single_pass_armed = false;
  // An opaque/evaluation-failure admission has no proven frontier. Capture
  // its complete stream in SHM first; a gaining run inserts it with
  // InsertTrace, while an overflow is replayed through full-pipe only after
  // AFL++ confirms the coverage gain.
  bool root_shm_capture = false;
  bool root_shm_enabled = true;
  int full_stream_read_fd = -1;
  int full_stream_write_fd = -1;

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
  uint64_t single_pass_captures = 0;
  uint64_t single_pass_overflows = 0;

  // replay checker (SYMAFL_REPLAY_CHECK=1)
  bool replay_check = false;
  uint64_t replay_checked = 0;
  uint64_t replay_cid_mismatch = 0;
  uint64_t replay_direction_mismatch = 0;
  uint64_t replay_after_terminal = 0;
  uint64_t replay_truncated = 0;
  uint64_t replay_frontier_match = 0;
  uint64_t replay_terminal_match = 0;

  // segmented profiling (SYMAFL_PROFILE=1), default off
  bool profile_enabled = false;
  uint64_t profile_check_ns = 0;
  uint64_t profile_check_calls = 0;
  uint64_t profile_trace_ns = 0;
  uint64_t profile_trace_calls = 0;
  uint64_t profile_decode_ns = 0;   // suffix decode (SHM -> Event vector)
  uint64_t profile_decode_calls = 0;
  uint64_t profile_insert_ns = 0;   // InsertSuffix (label->predicate + arena)
  uint64_t profile_insert_calls = 0;
  uint64_t profile_replay_ns = 0;
  uint64_t profile_replay_calls = 0;

  // Veto-probe (SYMAFL_VETO_PROBE_EVERY=N, default 0=off): execute every Nth
  // vetoed candidate as a measurement probe so we can observe whether the
  // screening is incorrectly vetoing would-be coverage-gaining inputs. Probes
  // do not arm capture and never grow the tree.
  uint64_t veto_probe_every = 0;
  uint64_t veto_probe_count = 0;
  uint64_t veto_probe_admitted = 0;
  uint64_t veto_probe_gained = 0;
  // Probe-gain classification by veto kind (0 = terminal-class, 1 = rlimit),
  // mirroring last_veto_kind. Kept aggregated so the exact-probe census can
  // report which veto class actually loses coverage gains.
  uint64_t probe_gained_terminal = 0;
  uint64_t probe_gained_rlimit = 0;
  // Optional feedback path: a coverage-gaining probe from an unexplored
  // rlimit edge may insert its suffix at the exact saved frontier. Terminal
  // edges are never reopened by this path.
  bool probe_learn = false;
  bool probe_capture_pending = false;
  pcbt::NodeRef probe_capture_node = pcbt::kUnexplored;
  uint8_t probe_capture_dir = 0;
  uint64_t probe_learned = 0;
  uint64_t probe_learn_failed = 0;
  bool last_was_probe = false;

  // Probe/screening diagnostic (SYMAFL_PROBE_DIAG=1): probes arm suffix
  // capture at the veto depth, so we can classify what the vetoed population
  // actually does past the terminal prefix: an empty suffix means the
  // decision trace really terminates there (bitmap gains are event-free
  // divergence, structural); a nonempty suffix means the tree's terminal
  // judgment was wrong (screening defect, fixable). Admitted runs are also
  // measured: how many execute a decision-bearing suffix past the frontier
  // without any bitmap gain (tree gain without coverage gain).
  bool probe_diag = false;
  uint64_t diag_probe_suffix_empty = 0;    // veto: no decisions past terminal
  uint64_t diag_probe_suffix_nonempty = 0; // veto: decisions past terminal
  uint64_t diag_probe_suffix_overflow = 0;
  uint64_t diag_probe_suffix_events = 0;
  uint64_t diag_admit_suffix_empty = 0;    // admit: no decisions past frontier
  uint64_t diag_admit_suffix_nonempty = 0; // admit: decisions past frontier
  uint64_t diag_admit_suffix_overflow = 0;
  uint64_t diag_admit_suffix_events = 0;
  // Veto depth buckets (16-deep buckets, >=256 in the last one).
  uint64_t diag_veto_depth[17] = {};
  uint32_t last_veto_depth = 0;
  pcbt::NodeRef last_veto_node = pcbt::kUnexplored;
  uint8_t last_veto_kind = 0;         // 0 = terminal-class, 1 = rlimit
  uint8_t last_probe_veto_kind = 0;   // veto kind of the last probe candidate
  uint8_t last_probe_input[64] = {};
  uint32_t last_probe_input_len = 0;
  // Saturation via probe-gain windows (SYMAFL_SAT_WINDOW / SYMAFL_SAT_MIN_GAINS,
  // default off): once a window of probe outcomes yields fewer than
  // sat_min_gains coverage gains, the vetoed population no longer carries
  // exploitable event-free divergence and the tree's screening marginal value
  // is exhausted; the run switches to the concrete target (baseline speed).
  uint64_t sat_window = 0;
  uint64_t sat_min_gains = 0;
  uint64_t sat_consec = 0;        // consecutive low-gain windows required
  uint64_t sat_probe_total = 0;   // probes observed since last check
  uint64_t sat_probe_gained = 0;  // gains among them
  uint64_t sat_low_windows = 0;   // consecutive windows below min_gains
  // Hard concolic-phase deadline (SYMAFL_CONCOLIC_SECONDS=N): switch to the
  // concrete target after N seconds of screening, independent of probe-gain
  // windows, so the phase transition is reproducible across runs. The
  // adaptive window can still trigger an earlier switch.
  uint64_t concolic_deadline = 0;
  time_t phase_start = 0;
  // Per-probe linkage: whether the executed probe had a decision-bearing
  // suffix past the veto depth (screening defect class) and its input length.
  bool last_probe_suffix_nonempty = false;
  bool last_probe_suffix_overflow = false;
  uint32_t last_probe_len = 0;
  uint64_t probe_gained_nonempty = 0;
  uint64_t probe_gained_empty = 0;
  uint64_t probe_gained_overflow = 0;
  uint64_t diag_probe_details = 0;  // printed nonempty-probe details

  // Pair forensics (SYMAFL_PAIR_LOG=<path>): record every admitted run's
  // input at its (node, dir) admission edge. A later vetoed-but-gainful
  // candidate at veto node N with evaluated direction d has its admitted
  // counterpart recorded at (N, d) -- the run that created the terminal
  // edge -- with the identical PCBT path. Both streams replayed through the
  // concolic target expose the decision the tree missed.
  FILE *pair_log = nullptr;
  // SYMAFL_PROBE_GAINED_LOG: append-only list of queue filenames that were
  // vetoed, probe-executed, and gained coverage. Used for end-of-run bitmap
  // checks: does the gain survive to the final bitmap, or was it superseded?
  FILE *probe_gained_log = nullptr;
  // Optional low-overhead progress stream for terminal-state experiments.
  // Rows are monotonic milliseconds and cumulative candidate counters; the
  // supervisor uses these rows to test five-minute throughput stability.
  FILE *progress_log = nullptr;
  uint64_t progress_interval_ms = 5000;
  uint64_t progress_last_ms = 0;
  uint64_t progress_calls = 0;
  uint8_t last_veto_dir = 0;
};

// Shared union table owned by the target forkserver.
static dfsan_label_info *__dfsan_label_info;
static const size_t MAX_LABEL = uniontable_size / sizeof(dfsan_label_info);

dfsan_label_info *__dfsan::get_label_info(dfsan_label label) {
  if (unlikely(label >= MAX_LABEL)) {
    throw std::out_of_range("label too large " + std::to_string(label));
  }
  return &__dfsan_label_info[label];
}

// Optional segmented profiling (SYMAFL_PROFILE=1), default off. Segments
// accumulate monotonic nanoseconds plus call counts without touching the
// clock while profiling is disabled, and never alter PCBT decisions,
// insertion, transport, or phase switching.
static inline uint64_t profile_now() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static inline uint64_t monotonic_ms() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)ts.tv_nsec / 1000000ULL;
}

static void write_progress(my_mutator_t *data, bool force) {
  if (!data->progress_log) return;
  ++data->progress_calls;
  if (!force && (data->progress_calls & 255u) != 0) return;
  const uint64_t now = monotonic_ms();
  if (!force && data->progress_last_ms &&
      now - data->progress_last_ms < data->progress_interval_ms) return;
  data->progress_last_ms = now;
  fprintf(data->progress_log, "%llu\t%llu\t%llu\t%llu\t%d\n",
          (unsigned long long)now, (unsigned long long)data->screened,
          (unsigned long long)data->admitted,
          (unsigned long long)data->vetoed, data->screening ? 1 : 0);
  fflush(data->progress_log);
}

static inline uint64_t profile_start(my_mutator_t *data) {
  return data->profile_enabled ? profile_now() : 0;
}

static inline void profile_stop(my_mutator_t *data, uint64_t start,
                                uint64_t *ns, uint64_t *calls) {
  if (data->profile_enabled) {
    *ns += profile_now() - start;
    *calls += 1;
  }
}

// RAII segment covering every exit of the enclosing function, including
// early returns. Nested inside replay_pipe_suffix, the inner trace segment
// also accumulates, so trace_* can be a subset of replay_* for replays.
class ProfileSegment {
 public:
  ProfileSegment(my_mutator_t *data, uint64_t *ns, uint64_t *calls)
      : data_(data), ns_(ns), calls_(calls), start_(profile_start(data)) {}
  ~ProfileSegment() { profile_stop(data_, start_, ns_, calls_); }

 private:
  my_mutator_t *data_;
  uint64_t *ns_;
  uint64_t *calls_;
  uint64_t start_;
};

static bool check_input_timed(my_mutator_t *data, const u8 *buf,
                              uint32_t buf_size, pcbt::NodeRef *node,
                              uint8_t *dir, uint32_t *veto_depth = nullptr,
                              pcbt::NodeRef *veto_node = nullptr,
                              uint8_t *veto_dir = nullptr,
                              uint8_t *veto_kind = nullptr) {
  uint64_t start = profile_start(data);
  bool admitted = data->tree.CheckInput(buf, buf_size, node, dir,
                                        data->rlimit, veto_depth, veto_node,
                                        veto_dir, veto_kind);
  profile_stop(data, start, &data->profile_check_ns,
               &data->profile_check_calls);
  return admitted;
}

static void print_concolic_phase_snapshot(const my_mutator_t *data) {
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt-concolic-phase] screened=%llu admitted=%llu "
          "vetoed=%llu traced_entries=%llu probe_admitted=%llu "
          "probe_gained=%llu admit_frontier=%llu admit_len_veto=%llu "
          "veto_terminal=%llu veto_rlimit=%llu "
          "probe_gained_terminal=%llu probe_gained_rlimit=%llu "
          "traces=%llu nodes=%llu depth=%llu\n",
          (unsigned long long)data->screened,
          (unsigned long long)data->admitted,
          (unsigned long long)data->vetoed,
          (unsigned long long)data->traced_entries.size(),
          (unsigned long long)data->veto_probe_admitted,
          (unsigned long long)data->veto_probe_gained,
          (unsigned long long)t.check_admit_frontier,
          (unsigned long long)t.check_admit_len_veto,
          (unsigned long long)t.check_veto_terminal,
          (unsigned long long)t.check_veto_rlimit,
          (unsigned long long)data->probe_gained_terminal,
          (unsigned long long)data->probe_gained_rlimit,
          (unsigned long long)t.num_traces,
          (unsigned long long)t.num_nodes,
          (unsigned long long)t.max_depth);
}

static void init_forkserver_capture(my_mutator_t *data) {
  uint32_t capacity = 1U << 20;
  if (const char *value = getenv("SYMAFL_SINGLE_PASS_CAPACITY")) {
    char *end = nullptr;
    unsigned long long parsed = strtoull(value, &end, 10);
    if (end == value || *end != '\0' || parsed == 0 ||
        parsed > UINT32_MAX) {
      FATAL("Invalid SYMAFL_SINGLE_PASS_CAPACITY=%s", value);
    }
    capacity = (uint32_t)parsed;
  }

  data->single_pass_size = symafl_single_pass_size(capacity);
  data->single_pass_union_name =
      alloc_printf("/symafl-single-pass-union-%d", getpid());
  data->single_pass_trace_name =
      alloc_printf("/symafl-single-pass-events-%d", getpid());
  data->single_pass_union_fd = shm_open(data->single_pass_union_name,
      O_RDWR | O_CREAT | O_EXCL, S_IRUSR | S_IWUSR);
  if (data->single_pass_union_fd < 0 ||
      ftruncate(data->single_pass_union_fd, uniontable_size)) {
    PFATAL("Failed to create single-pass union table");
  }
  data->single_pass_label_info = (dfsan_label_info *)mmap(
      nullptr, uniontable_size, PROT_READ, MAP_SHARED,
      data->single_pass_union_fd, 0);
  if (data->single_pass_label_info == MAP_FAILED) {
    data->single_pass_label_info = nullptr;
    PFATAL("Failed to map single-pass union table");
  }
  data->single_pass_trace_fd = shm_open(data->single_pass_trace_name,
      O_RDWR | O_CREAT | O_EXCL, S_IRUSR | S_IWUSR);
  if (data->single_pass_trace_fd < 0 ||
      ftruncate(data->single_pass_trace_fd, data->single_pass_size)) {
    PFATAL("Failed to create single-pass event buffer");
  }
  data->single_pass_control = (symafl_single_pass_control *)mmap(
      nullptr, data->single_pass_size, PROT_READ | PROT_WRITE, MAP_SHARED,
      data->single_pass_trace_fd, 0);
  if (data->single_pass_control == MAP_FAILED) {
    data->single_pass_control = nullptr;
    PFATAL("Failed to map single-pass event buffer");
  }
  memset(data->single_pass_control, 0, data->single_pass_size);
  data->single_pass_control->magic = SYMAFL_SINGLE_PASS_MAGIC;
  data->single_pass_control->version = SYMAFL_SINGLE_PASS_VERSION;
  data->single_pass_control->event_capacity = capacity;

  int pipefd[2];
  if (pipe(pipefd)) PFATAL("Failed to create forkserver full-trace pipe");
  data->full_stream_read_fd = pipefd[0];
  data->full_stream_write_fd = pipefd[1];
  int flags = fcntl(data->full_stream_read_fd, F_GETFL);
  if (flags < 0 || fcntl(data->full_stream_read_fd, F_SETFL,
                         flags | O_NONBLOCK)) {
    PFATAL("Failed to configure forkserver full-trace pipe");
  }
  data->afl->fsrv.sym_trace_fd = data->full_stream_read_fd;

  const char *old_options = getenv("TAINT_OPTIONS");
  char *pipe_option = alloc_printf(":pipe_fd=%d", data->full_stream_write_fd);
  char *options = alloc_printf(
      "%s%sshm_name=%s:shm_size=%zu:single_pass_name=%s:single_pass_size=%zu"
      "%s",
      old_options ? old_options : "", old_options && *old_options ? ":" : "",
      data->single_pass_union_name, uniontable_size,
      data->single_pass_trace_name, data->single_pass_size,
      pipe_option ? pipe_option : "");
  if (setenv("TAINT_OPTIONS", options, 1)) {
    if (pipe_option) ck_free(pipe_option);
    ck_free(options);
    PFATAL("Failed to configure single-pass TAINT_OPTIONS");
  }
  if (pipe_option) ck_free(pipe_option);
  ck_free(options);
  __dfsan_label_info = data->single_pass_label_info;
  fprintf(stderr, "[pcbt] forkserver trace control enabled (capacity=%u)\n",
          capacity);
}

/// no splice input
extern "C" void afl_custom_splice_optout(my_mutator_t *data) {
  (void)(data);
}

extern "C" my_mutator_t *afl_custom_init(afl_state *afl, unsigned int seed) {
  (void)(seed);

  my_mutator_t *data = new my_mutator_t(afl);
  if (!data) {
    FATAL("afl_custom_init alloc");
    return NULL;
  }

  // PCBT has two distinct execution phases. The initial target must be the
  // concolic binary; after the tree is exhausted AFL++ restarts its
  // forkserver with the concrete binary and rebuilds coverage from the queue.
  const char *concolic = getenv("SYMAFL_CONCOLIC_TARGET");
  const char *concrete = getenv("SYMAFL_CONCRETE_TARGET");
  if (!concolic || !*concolic || !concrete || !*concrete) {
    FATAL("PCBT mode requires SYMAFL_CONCOLIC_TARGET and "
          "SYMAFL_CONCRETE_TARGET");
  }
  if (access(concolic, X_OK) || access(concrete, X_OK)) {
    PFATAL("PCBT target is not executable");
  }
  data->afl->pcbt_mode = 1;
  data->afl->pcbt_concrete_target = ck_strdup((u8 *)concrete);

  if (const char *mode = getenv("SYMAFL_TRACE_MODE")) {
    WARNF("SYMAFL_TRACE_MODE=%s is ignored: PCBT transport is selected "
          "by lifecycle (bootstrap=pipe-full, steady=shm-suffix, "
          "overflow+gain=pipe-suffix)\n", mode);
  }
  init_forkserver_capture(data);

  if (getenv("SYMAFL_REPLAY_CHECK")) {
    data->replay_check = true;
    fprintf(stderr, "[pcbt] replay check enabled: all admitted candidates "
            "use full-pipe capture and trace replay validation\n");
  }
  if (getenv("SYMAFL_NO_SCREEN")) {
    data->screening = false;
  }
  if (const char *root_shm = getenv("SYMAFL_ROOT_SHM")) {
    data->root_shm_enabled = strcmp(root_shm, "0") != 0;
    fprintf(stderr, "[pcbt] root SHM capture %s (SYMAFL_ROOT_SHM=%s)\n",
            data->root_shm_enabled ? "enabled" : "disabled", root_shm);
  }
  if (getenv("SYMAFL_PROFILE")) {
    data->profile_enabled = true;
    data->tree.set_profile(true);
    fprintf(stderr, "[pcbt] profiling enabled (SYMAFL_PROFILE=1)\n");
  }
  if (getenv("SYMAFL_PCBT_DEBUG")) {
    data->tree.set_debug(true);
    fprintf(stderr, "[pcbt] predicate debug enabled (SYMAFL_PCBT_DEBUG=1)\n");
  }
  if (const char *rl = getenv("SYMAFL_RCNT_LIMIT")) {
    char *end = nullptr;
    unsigned long parsed = strtoul(rl, &end, 10);
    if (end == rl || *end != '\0' || parsed > UINT8_MAX) {
      FATAL("Invalid SYMAFL_RCNT_LIMIT=%s (expected 0..255)", rl);
    }
    data->rlimit = (uint8_t)parsed;
  }
  if (const char *vp = getenv("SYMAFL_VETO_PROBE_EVERY")) {
    char *end = nullptr;
    unsigned long long parsed = strtoull(vp, &end, 10);
    if (end == vp || *end != '\0' || parsed == 0 ||
        parsed > UINT64_MAX) {
      FATAL("Invalid SYMAFL_VETO_PROBE_EVERY=%s", vp);
    }
    data->veto_probe_every = parsed;
    fprintf(stderr, "[pcbt] veto probe enabled: execute every %lluth "
            "vetoed candidate to measure incorrect-veto rate\n",
            (unsigned long long)parsed);
  }
  if (getenv("SYMAFL_PROBE_DIAG")) {
    data->probe_diag = true;
    fprintf(stderr, "[pcbt] probe diagnostic enabled (SYMAFL_PROBE_DIAG=1)\n");
  }
  if (getenv("SYMAFL_PROBE_LEARN")) {
    data->probe_learn = true;
    fprintf(stderr, "[pcbt] rlimit probe learning enabled; terminal edges "
                    "remain immutable\n");
  }
  if (const char *pl = getenv("SYMAFL_PAIR_LOG")) {
    data->pair_log = fopen(pl, "w");
    if (!data->pair_log) {
      FATAL("cannot open SYMAFL_PAIR_LOG=%s", pl);
    }
    fprintf(stderr, "[pcbt] pair forensics log: %s\n", pl);
  }
  if (const char *pgl = getenv("SYMAFL_PROBE_GAINED_LOG")) {
    data->probe_gained_log = fopen(pgl, "w");
    if (!data->probe_gained_log) {
      FATAL("cannot open SYMAFL_PROBE_GAINED_LOG=%s", pgl);
    }
    fprintf(stderr, "[pcbt] probe-gained log: %s\n", pgl);
  }
  if (const char *progress = getenv("SYMAFL_PROGRESS_LOG")) {
    data->progress_log = fopen(progress, "w");
    if (!data->progress_log) {
      FATAL("cannot open SYMAFL_PROGRESS_LOG=%s", progress);
    }
    if (const char *interval = getenv("SYMAFL_PROGRESS_INTERVAL_MS")) {
      char *end = nullptr;
      unsigned long long parsed = strtoull(interval, &end, 10);
      if (end == interval || *end != '\0' || parsed == 0) {
        FATAL("Invalid SYMAFL_PROGRESS_INTERVAL_MS=%s", interval);
      }
      data->progress_interval_ms = parsed;
    }
    fprintf(stderr, "[pcbt] progress log: %s (interval=%llums)\n", progress,
            (unsigned long long)data->progress_interval_ms);
  }
  if (const char *cd = getenv("SYMAFL_CONCOLIC_SECONDS")) {
    char *end = nullptr;
    unsigned long long parsed = strtoull(cd, &end, 10);
    if (end == cd || *end != '\0' || parsed == 0) {
      FATAL("Invalid SYMAFL_CONCOLIC_SECONDS=%s", cd);
    }
    data->concolic_deadline = parsed;
    fprintf(stderr, "[pcbt] concolic phase deadline: %llus\n",
            (unsigned long long)parsed);
  }
  if (const char *sw = getenv("SYMAFL_SAT_WINDOW")) {
    char *end = nullptr;
    unsigned long long parsed = strtoull(sw, &end, 10);
    if (end == sw || *end != '\0' || parsed == 0) {
      FATAL("Invalid SYMAFL_SAT_WINDOW=%s", sw);
    }
    data->sat_window = parsed;
    const char *mg = getenv("SYMAFL_SAT_MIN_GAINS");
    if (!mg) {
      FATAL("SYMAFL_SAT_WINDOW requires SYMAFL_SAT_MIN_GAINS");
    }
    char *mgend = nullptr;
    unsigned long long mgparsed = strtoull(mg, &mgend, 10);
    if (mgend == mg || *mgend != '\0') {
      FATAL("Invalid SYMAFL_SAT_MIN_GAINS=%s", mg);
    }
    data->sat_min_gains = mgparsed;
    const char *sc = getenv("SYMAFL_SAT_CONSEC");
    data->sat_consec = sc ? strtoull(sc, nullptr, 10) : 1;
    fprintf(stderr, "[pcbt] probe-gain saturation window enabled: "
            "window=%llu min_gains=%llu consec=%llu\n",
            (unsigned long long)parsed, (unsigned long long)mgparsed,
            (unsigned long long)data->sat_consec);
  }
  return data;
}

extern "C" void afl_custom_deinit(my_mutator_t *data) {
  write_progress(data, true);
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt] traces=%llu nodes=%llu pred_nodes=%llu depth=%llu conflicts=%llu "
          "opaque=%llu failed=%llu timeouts=%llu memerr=%llu screened=%llu "
          "admitted=%llu vetoed=%llu traced_entries=%llu saturated=%llu "
          "single_pass=%llu single_pass_overflow=%llu "
          "admit_empty=%llu admit_opaque=%llu admit_eval_failure=%llu admit_frontier=%llu "
          "admit_len_veto=%llu veto_terminal=%llu veto_rlimit=%llu probe_admitted=%llu probe_gained=%llu "
          "probe_gained_terminal=%llu probe_gained_rlimit=%llu profile=%d "
          "check_ns=%llu check_calls=%llu trace_ns=%llu trace_calls=%llu "
          "replay_ns=%llu replay_calls=%llu decode_ns=%llu decode_calls=%llu "
          "insert_ns=%llu insert_calls=%llu\n",
          (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
          (unsigned long long)t.num_pred_nodes(),
          (unsigned long long)t.max_depth,
          (unsigned long long)t.num_conflicts,
          (unsigned long long)t.num_opaque,
          (unsigned long long)data->failed_runs,
          (unsigned long long)data->trace_timeouts,
          (unsigned long long)data->memerr_events,
          (unsigned long long)data->screened,
          (unsigned long long)data->admitted,
          (unsigned long long)data->vetoed,
          (unsigned long long)data->traced_entries.size(),
          (unsigned long long)(data->screening ? 0 : 1),
          (unsigned long long)data->single_pass_captures,
          (unsigned long long)data->single_pass_overflows,
          (unsigned long long)t.check_admit_empty,
          (unsigned long long)t.check_admit_opaque,
          (unsigned long long)t.check_admit_eval_failure,
          (unsigned long long)t.check_admit_frontier,
          (unsigned long long)t.check_admit_len_veto,
          (unsigned long long)t.check_veto_terminal,
          (unsigned long long)t.check_veto_rlimit,
          (unsigned long long)data->veto_probe_admitted,
          (unsigned long long)data->veto_probe_gained,
          (unsigned long long)data->probe_gained_terminal,
          (unsigned long long)data->probe_gained_rlimit,
          (int)(data->profile_enabled ? 1 : 0),
          (unsigned long long)data->profile_check_ns,
          (unsigned long long)data->profile_check_calls,
          (unsigned long long)data->profile_trace_ns,
          (unsigned long long)data->profile_trace_calls,
          (unsigned long long)data->profile_replay_ns,
          (unsigned long long)data->profile_replay_calls,
          (unsigned long long)data->profile_decode_ns,
          (unsigned long long)data->profile_decode_calls,
          (unsigned long long)data->profile_insert_ns,
          (unsigned long long)data->profile_insert_calls);
  if (data->profile_enabled) {
    const uint64_t calls = data->profile_check_calls;
    fprintf(stderr,
            "[pcbt-profile] checks=%llu walk_nodes=%llu predicate_calls=%llu "
            "computed_nodes=%llu cache_hits=%llu read_nodes=%llu "
            "read_bytes=%llu exit_depth_sum="
            "empty:%llu,opaque:%llu,eval_failure:%llu,frontier:%llu,"
            "terminal:%llu,rlimit:%llu\n",
            (unsigned long long)calls,
            (unsigned long long)t.profile_check_node_visits,
            (unsigned long long)t.profile_check_predicate_calls,
            (unsigned long long)t.profile_check_computed_nodes,
            (unsigned long long)t.profile_check_cache_hits,
            (unsigned long long)t.profile_check_read_nodes,
            (unsigned long long)t.profile_check_read_bytes,
            (unsigned long long)t.profile_check_exit_depth[0],
            (unsigned long long)t.profile_check_exit_depth[1],
            (unsigned long long)t.profile_check_exit_depth[2],
            (unsigned long long)t.profile_check_exit_depth[3],
            (unsigned long long)t.profile_check_exit_depth[4],
            (unsigned long long)t.profile_check_exit_depth[5]);
    (void)calls;
  }
  fprintf(stderr,
          "[pcbt-replay] checked=%llu cid_mismatch=%llu dir_mismatch=%llu "
          "after_terminal=%llu truncated=%llu frontier_match=%llu "
          "terminal_match=%llu\n",
          (unsigned long long)data->replay_checked,
          (unsigned long long)data->replay_cid_mismatch,
          (unsigned long long)data->replay_direction_mismatch,
          (unsigned long long)data->replay_after_terminal,
          (unsigned long long)data->replay_truncated,
          (unsigned long long)data->replay_frontier_match,
          (unsigned long long)data->replay_terminal_match);
  fprintf(stderr,
          "[pcbt-opaque] invalid_root=%llu invalid_label=%llu initializing_label=%llu "
          "invalid_width=%llu depth_limit=%llu bad_load=%llu bad_concat=%llu "
          "unsupported_op=%llu unsupported_compare=%llu uncaptured_memcmp_operand=%llu "
          "arena_limit=%llu node_limit=%llu\n",
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::InvalidRoot],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::InvalidLabel],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::InitializingLabel],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::InvalidWidth],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::DepthLimit],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::BadLoad],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::BadConcat],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::UnsupportedOp],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::UnsupportedCompare],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::UncapturedMemcmpOperand],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::ArenaLimit],
          (unsigned long long)t.opaque_by_error[(size_t)pcbt::PredError::NodeLimit]);
  for (const auto &entry : t.opaque_by_op) {
    fprintf(stderr, "[pcbt-opaque-op] op=%u count=%llu\n", entry.first,
            (unsigned long long)entry.second);
  }
  if (!t.opaque_by_cid.empty()) {
    std::vector<std::pair<uint32_t, uint64_t>> by_cid(
        t.opaque_by_cid.begin(), t.opaque_by_cid.end());
    std::sort(by_cid.begin(), by_cid.end(),
              [](const auto &a, const auto &b) {
                if (a.second != b.second) return a.second > b.second;
                return a.first < b.first;
              });
    const size_t limit = std::min<size_t>(by_cid.size(), 32);
    for (size_t i = 0; i < limit; ++i) {
      fprintf(stderr, "[pcbt-opaque-cid] cid=%u count=%llu\n",
              by_cid[i].first, (unsigned long long)by_cid[i].second);
    }
  }
  // Tree topology dump for offline pair/terminal forensics
  // (SYMAFL_TREE_DUMP=<path>).
  if (const char *dump = getenv("SYMAFL_TREE_DUMP")) {
    data->tree.Dump(dump);
    fprintf(stderr, "[pcbt] tree dump -> %s\n", dump);
  }
  // Step-by-step CheckInput evaluation of one candidate
  // (SYMAFL_EVAL_INPUT=<file>): prints every visited node (cid/skip/depth)
  // and the evaluated direction, to see where a candidate should have
  // forked from the tree path but did not.
  if (const char *eval = getenv("SYMAFL_EVAL_INPUT")) {
    FILE *f = fopen(eval, "rb");
    if (!f) {
      fprintf(stderr, "[pcbt] cannot open SYMAFL_EVAL_INPUT=%s\n", eval);
    } else {
      std::vector<u8> buf;
      uint8_t chunk[65536];
      size_t n;
      while ((n = fread(chunk, 1, sizeof(chunk), f)) > 0) {
        buf.insert(buf.end(), chunk, chunk + n);
      }
      fclose(f);
      data->tree.set_debug(true);
      pcbt::NodeRef node = pcbt::kUnexplored;
      uint8_t dir = 0;
      uint32_t vdepth = 0;
      pcbt::NodeRef vnode = pcbt::kUnexplored;
      uint8_t vdir = 0, vkind = 0;
      bool adm = data->tree.CheckInput(buf.data(), (uint32_t)buf.size(),
                                       &node, &dir, data->rlimit, &vdepth,
                                       &vnode, &vdir, &vkind);
      fprintf(stderr,
              "[pcbt-eval] %s admitted=%d node=%u dir=%u veto_node=%u "
              "veto_dir=%u veto_depth=%u veto_kind=%u\n",
              eval, adm ? 1 : 0, node, dir, vnode, vdir, vdepth, vkind);
      data->tree.set_debug(false);
    }
  }
  if (data->probe_diag) {
    fprintf(stderr,
            "[pcbt-diag] probe_suffix_empty=%llu probe_suffix_nonempty=%llu "
            "probe_suffix_overflow=%llu probe_suffix_events=%llu "
            "admit_suffix_empty=%llu admit_suffix_nonempty=%llu "
            "admit_suffix_overflow=%llu admit_suffix_events=%llu "
            "probe_gained_nonempty=%llu probe_gained_empty=%llu "
            "probe_gained_overflow=%llu veto_depth_buckets=",
            (unsigned long long)data->diag_probe_suffix_empty,
            (unsigned long long)data->diag_probe_suffix_nonempty,
            (unsigned long long)data->diag_probe_suffix_overflow,
            (unsigned long long)data->diag_probe_suffix_events,
            (unsigned long long)data->diag_admit_suffix_empty,
            (unsigned long long)data->diag_admit_suffix_nonempty,
            (unsigned long long)data->diag_admit_suffix_overflow,
            (unsigned long long)data->diag_admit_suffix_events,
            (unsigned long long)data->probe_gained_nonempty,
            (unsigned long long)data->probe_gained_empty,
            (unsigned long long)data->probe_gained_overflow);
    for (size_t i = 0; i < 17; ++i) {
      fprintf(stderr, "%llu%s", (unsigned long long)data->diag_veto_depth[i],
              i + 1 < 17 ? "," : "\n");
    }
  }
  if (data->pair_log) fclose(data->pair_log);
  if (data->probe_gained_log) fclose(data->probe_gained_log);
  delete data;
}


static void disarm_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELEASE);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_OFF, __ATOMIC_RELEASE);
  data->single_pass_armed = false;
  data->root_shm_capture = false;
}

static void arm_full_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_FULL_STREAM, __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->single_pass_armed = true;
  data->root_shm_capture = false;
}

static void arm_root_shm_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  control->skip_depth = 0;
  __atomic_store_n(&control->mode, SYMAFL_TRACE_SUFFIX_SHM,
                   __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->single_pass_armed = true;
  data->root_shm_capture = true;
}

static void arm_suffix_capture(my_mutator_t *data, pcbt::NodeRef node,
                               uint8_t dir) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  // A constraint node's dir-1 (pinned-value) edge is explored the moment
  // the node is created (it holds the creating candidate's follow-up or is
  // terminal), so an admission on that edge never occurs and the capture
  // always starts at the parent's skipCnt. The value-fork direction
  // (dir-0) captures the candidate's own decision event and extends the
  // chain.
  control->skip_depth = data->tree.skip_for(node, dir);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_SUFFIX_SHM, __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->last_node = node;
  data->last_dir = dir;
  data->single_pass_armed = true;
  data->root_shm_capture = false;
}

static void arm_pipe_suffix_capture(my_mutator_t *data, pcbt::NodeRef node,
                                    uint8_t dir) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  control->skip_depth = data->tree.skip_for(node, dir);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_SUFFIX_PIPE,
                   __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->last_node = node;
  data->last_dir = dir;
  data->single_pass_armed = true;
  data->root_shm_capture = false;
}

static bool decode_full_stream(const u8 *wire, size_t wire_size,
                               std::vector<pcbt::Event> *events) {
  size_t offset = 0;
  size_t n_cond = 0, n_dropped_zero = 0, n_dropped_init = 0;
  while (offset < wire_size) {
    if (wire_size - offset < sizeof(pipe_msg)) return false;
    pipe_msg msg;
    memcpy(&msg, wire + offset, sizeof(msg));
    offset += sizeof(msg);
    if (msg.msg_type == cond_type) {
      n_cond++;
      if (msg.label == 0) { n_dropped_zero++; continue; }
      if (msg.label == kInitializingLabel) { n_dropped_init++; continue; }
      if (msg.label >= MAX_LABEL) return false;
      uint8_t is_constraint = (msg.flags & F_CONSTRAINT) ? 1 : 0;
      events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0),
                         is_constraint, 1});
      continue;
    }
    if (msg.msg_type == fold_type) {
      // Fold frame: `count` consecutive conditions with the same cid/result
      // and a byte-advancing Read-family shape. The mutator expands it when
      // inserting (no synthetic labels exist for the intermediate events).
      n_cond++;
      if (msg.count < 2 || msg.count > SYMAFL_MAX_FOLD_COUNT) return false;
      if (msg.label == 0) { n_dropped_zero++; continue; }
      if (msg.label == kInitializingLabel) { n_dropped_init++; continue; }
      if (msg.label >= MAX_LABEL) return false;
      events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0), 0,
                         (uint16_t)msg.count});
      continue;
    }
    size_t trailer = 0;
    if (msg.msg_type == gep_type) {
      trailer = sizeof(gep_msg);
    } else if (msg.msg_type == memcmp_type && msg.flags) {
      trailer = sizeof(memcmp_msg) + (size_t)msg.result;
    } else if (msg.msg_type == gv_type) {
      trailer = (size_t)msg.result;
    }
    if (trailer > wire_size - offset) return false;
    offset += trailer;
  }
  fprintf(stderr, "[pcbt-debug] decode: bytes=%zu cond=%zu dropped_zero=%zu "
          "dropped_init=%zu kept=%zu\n",
          wire_size, n_cond, n_dropped_zero, n_dropped_init,
          events->size());
  return true;
}

static bool decode_pipe_events(my_mutator_t *data,
                               std::vector<pcbt::Event> *events,
                               const char *fname) {
  afl_forkserver_t *fsrv = &data->afl->fsrv;
  if (decode_full_stream(fsrv->sym_trace_buf, fsrv->sym_trace_len, events)) {
    return true;
  }
  WARNF("invalid pipe trace for %s (%zu bytes)\n", fname,
        fsrv->sym_trace_len);
  data->failed_runs += 1;
  return false;
}

// The label table belongs to the just-finished child.  On replay failure, dump
// the complete reachable DAG before that table is reused by the next child.
// `seen` makes shared subexpressions explicit and also protects this
// diagnostic path from malformed cyclic label metadata.
static void dump_label_dag(dfsan_label root) {
  if (root == 0 || root == kInitializingLabel || root >= MAX_LABEL) return;

  std::vector<uint8_t> seen(MAX_LABEL, 0);
  std::vector<dfsan_label> stack = {root};
  while (!stack.empty()) {
    dfsan_label label = stack.back();
    stack.pop_back();
    if (label == 0 || label == kInitializingLabel || label >= MAX_LABEL) {
      continue;
    }
    if (seen[label]) {
      fprintf(stderr, "[pcbt-dbg]   label=%u repeat\n", label);
      continue;
    }
    seen[label] = 1;

    const dfsan_label_info &info = __dfsan_label_info[label];
    const uint16_t base_op = info.op & 0xff;
    const uint32_t packed_predicate = info.op >> 8;
    fprintf(stderr,
            "[pcbt-dbg]   label=%u op=%u base_op=%u predicate=%u size=%u "
            "l1=%u l2=%u op1=%llu op2=%llu\n",
            label, info.op, base_op, packed_predicate, info.size, info.l1,
            info.l2, (unsigned long long)info.op1.i,
            (unsigned long long)info.op2.i);

    // Push l2 first so the printed traversal keeps l1 before l2.
    if (info.l2 != 0 && info.l2 != kInitializingLabel) stack.push_back(info.l2);
    if (info.l1 != 0 && info.l1 != kInitializingLabel) stack.push_back(info.l1);
  }
}

static bool replay_check_trace(my_mutator_t *data,
                               const std::vector<pcbt::Event> &events,
                               const u8 *buf, size_t buf_size,
                               const char *fname, bool is_suffix) {
  if (!data->replay_check) return true;
  if (events.empty()) return true;  // empty trace, nothing to check

  data->replay_checked += 1;
  auto report = data->tree.ReplayFullTrace(events, buf,
                                           (uint32_t)buf_size);

  if (report.error == pcbt::Tree::ReplayError::None) {
    if (report.reached_terminal) data->replay_terminal_match += 1;
    else if (report.reached_frontier) data->replay_frontier_match += 1;
    return true;
  }

  // Log the mismatch. The trace is discarded so it never grows the tree with
  // an unverified path; the divergence is a collection/derivation defect to
  // diagnose, not something the tree should learn around.
  const char *err_name = "unknown";
  switch (report.error) {
    case pcbt::Tree::ReplayError::CidMismatch:
      err_name = "cid_mismatch";
      data->replay_cid_mismatch += 1;
      break;
    case pcbt::Tree::ReplayError::DirectionMismatch:
      err_name = "direction_mismatch";
      data->replay_direction_mismatch += 1;
      break;
    case pcbt::Tree::ReplayError::AfterTerminal:
      err_name = "after_terminal";
      data->replay_after_terminal += 1;
      break;
    case pcbt::Tree::ReplayError::TruncatedTrace:
      err_name = "truncated";
      data->replay_truncated += 1;
      break;
    default: break;
  }
  WARNF("[pcbt-replay] %s mismatch %s at event=%zu verified=%zu "
        "expected_cid=%u observed_cid=%u eval_dir=%u obs_dir=%u %s\n",
        fname, err_name, report.event_index, report.verified_events,
        report.expected_cid, report.observed_cid,
        report.evaluated_dir, report.observed_dir,
        is_suffix ? "suffix" : "full");
  if (data->tree.debug() && report.event_index < events.size()) {
    // The mismatching event's label structure in the current run's union
    // table, plus the input bytes the stored predicate reads (DebugPredicate
    // above already dumped the node's reads and DAG).
    const pcbt::Event &ev = events[report.event_index];
    fprintf(stderr, "[pcbt-dbg] event idx=%zu cid=%u label=%u result=%u "
            "constraint=%u\n",
            report.event_index, ev.cid, ev.label, ev.result, ev.constraint);
    if (ev.label < MAX_LABEL && ev.label != 0 &&
        ev.label != kInitializingLabel) {
      const dfsan_label_info &li = __dfsan_label_info[ev.label];
      fprintf(stderr, "[pcbt-dbg] event label_info op=%u size=%u l1=%u l2=%u "
              "op1=%llu op2=%llu\n",
              li.op, li.size, li.l1, li.l2,
              (unsigned long long)li.op1.i, (unsigned long long)li.op2.i);
      dump_label_dag(ev.label);
    }
  }
  return false;  // discard mismatched trace
}

static bool insert_full_stream(my_mutator_t *data, const u8 *buf,
                               size_t buf_size, const char *fname,
                               pcbt::NodeRef *out_tail_node = nullptr,
                               uint8_t *out_tail_dir = nullptr) {
  ProfileSegment trace_seg(data, &data->profile_trace_ns,
                           &data->profile_trace_calls);
  std::vector<pcbt::Event> events;
  events.reserve(4096);
  if (!decode_pipe_events(data, &events, fname)) {
    disarm_capture(data);
    return false;
  }
  if (!replay_check_trace(data, events, buf, buf_size, fname, false)) {
    disarm_capture(data);
    return false;
  }
  uint32_t created = data->tree.InsertTrace(events, __dfsan_label_info,
                                            MAX_LABEL, buf,
                                            (uint32_t)buf_size,
                                            out_tail_node, out_tail_dir);
  data->traced_runs += 1;
  uint64_t expanded = 0;
  for (const pcbt::Event &ev : events) expanded += ev.count;
  fprintf(stderr, "[pcbt-trace] %s mode=full events=%zu expanded=%llu "
          "created=%u\n", fname, events.size(),
          (unsigned long long)expanded, created);
  disarm_capture(data);
  return true;
}

static bool insert_pipe_suffix_capture(my_mutator_t *data, const u8 *buf,
                                       size_t buf_size, const char *fname,
                                       pcbt::NodeRef *out_tail_node = nullptr,
                                       uint8_t *out_tail_dir = nullptr) {
  ProfileSegment trace_seg(data, &data->profile_trace_ns,
                           &data->profile_trace_calls);
  if (!data->single_pass_armed || data->last_node == pcbt::kUnexplored) {
    return false;
  }
  std::vector<pcbt::Event> events;
  events.reserve(4096);
  if (!decode_pipe_events(data, &events, fname)) {
    disarm_capture(data);
    return false;
  }
  uint32_t created = data->tree.InsertSuffix(data->last_node, data->last_dir,
      events, __dfsan_label_info, MAX_LABEL, out_tail_node, out_tail_dir);
  uint64_t expanded = 0;
  for (const pcbt::Event &ev : events) expanded += ev.count;
  fprintf(stderr,
          "[pcbt-trace] %s mode=pipe-suffix skip=%u events=%zu expanded=%llu "
          "created=%u\n",
          fname, data->tree.depth(data->last_node), events.size(),
          (unsigned long long)expanded, created);
  disarm_capture(data);
  return true;
}

static bool insert_suffix_capture(my_mutator_t *data, const u8 *buf,
                                  size_t buf_size, const char *fname,
                                  pcbt::NodeRef *out_tail_node = nullptr,
                                  uint8_t *out_tail_dir = nullptr) {
  ProfileSegment trace_seg(data, &data->profile_trace_ns,
                           &data->profile_trace_calls);
  if (!data->single_pass_armed ||
      (!data->root_shm_capture && data->last_node == pcbt::kUnexplored)) {
    return false;
  }
  bool root_capture = data->root_shm_capture;
  symafl_single_pass_control *control = data->single_pass_control;
  uint32_t count = __atomic_load_n(&control->event_count, __ATOMIC_ACQUIRE);
  bool overflow = __atomic_load_n(&control->overflow, __ATOMIC_ACQUIRE) ||
                  count > control->event_capacity;
  if (overflow) {
    data->single_pass_overflows += 1;
    WARNF("suffix capture overflow for %s; replaying through forkserver\n", fname);
    disarm_capture(data);
    return false;
  }
  std::vector<pcbt::Event> events;
  events.reserve(count);
  uint64_t decode_start = profile_start(data);
  for (uint32_t i = 0; i < count; ++i) {
    const symafl_single_pass_event &event = control->events[i];
    if (event.label == 0 || event.label == kInitializingLabel ||
        event.label >= MAX_LABEL) {
      disarm_capture(data);
      return false;
    }
    if (event.count != 0 && (event.count < 2 ||
                             event.count > SYMAFL_MAX_FOLD_COUNT)) {
      disarm_capture(data);
      return false;
    }
    uint16_t fold = event.count != 0 ? event.count : 1;
    events.push_back({event.cid, event.label, event.result,
                      event.constraint, fold});
  }
  profile_stop(data, decode_start, &data->profile_decode_ns,
               &data->profile_decode_calls);
  uint64_t insert_start = profile_start(data);
  uint32_t created = root_capture
      ? data->tree.InsertTrace(events, data->single_pass_label_info,
                               MAX_LABEL, buf, (uint32_t)buf_size,
                               out_tail_node, out_tail_dir)
      : data->tree.InsertSuffix(data->last_node, data->last_dir,
          events, data->single_pass_label_info, MAX_LABEL,
          out_tail_node, out_tail_dir);
  profile_stop(data, insert_start, &data->profile_insert_ns,
               &data->profile_insert_calls);
  data->single_pass_captures += 1;
  uint64_t expanded = 0;
  for (const pcbt::Event &ev : events) expanded += ev.count;
  fprintf(stderr,
          "[pcbt-trace] %s mode=%s skip=%u events=%zu expanded=%llu "
          "created=%u\n",
          fname, root_capture ? "root-shm" : "suffix",
          root_capture ? 0 : data->tree.depth(data->last_node), events.size(),
          (unsigned long long)expanded, created);
  disarm_capture(data);
  return true;
}

static bool replay_pipe_suffix(my_mutator_t *data, const u8 *buf,
                               size_t buf_size, const char *fname,
                               pcbt::NodeRef node, uint8_t dir) {
  ProfileSegment replay_seg(data, &data->profile_replay_ns,
                            &data->profile_replay_calls);
  arm_pipe_suffix_capture(data, node, dir);
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), buf_size);
  fsrv_run_result_t result = afl_fsrv_run_target(&data->afl->fsrv,
      data->afl->fsrv.exec_tmout, &data->afl->stop_soon);
  if (result != FSRV_RUN_OK) {
    WARNF("forkserver pipe-suffix replay failed for %s (%u)\n", fname,
          result);
    data->failed_runs += 1;
    disarm_capture(data);
    return false;
  }
  return insert_pipe_suffix_capture(data, buf, buf_size, fname);
}

static bool replay_full_capture(my_mutator_t *data, const u8 *buf,
                                size_t buf_size, const char *fname) {
  ProfileSegment replay_seg(data, &data->profile_replay_ns,
                            &data->profile_replay_calls);
  arm_full_capture(data);
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), buf_size);
  fsrv_run_result_t result = afl_fsrv_run_target(&data->afl->fsrv,
      data->afl->fsrv.exec_tmout, &data->afl->stop_soon);
  if (result != FSRV_RUN_OK) {
    WARNF("full-pipe replay failed for %s (%u)\n", fname, result);
    data->failed_runs += 1;
    disarm_capture(data);
    return false;
  }
  return insert_full_stream(data, buf, buf_size, fname);
}

static bool read_queue_file(const char *fname, std::vector<u8> *buf) {
  int fd = open(fname, O_RDONLY);
  struct stat st;
  if (fd < 0 || fstat(fd, &st) || st.st_size <= 0 || st.st_size > MAX_FILE) {
    if (fd >= 0) close(fd);
    return false;
  }
  buf->resize(st.st_size);
  ssize_t got = read(fd, buf->data(), buf->size());
  close(fd);
  return got == (ssize_t)buf->size();
}

// The bootstrap input is AFL's .cur_input; replay validation needs its real
// bytes and length (Len nodes evaluate against the candidate length, so a
// null buffer / zero length mispredicts length-boundary predicates).
static bool read_cur_input(my_mutator_t *data, std::vector<u8> *buf) {
  if (!data->afl->out_dir) return false;
  // AFL++ points out_dir at the per-fuzzer working directory (which ends in
  // "/default" for a single fuzzer); .cur_input lives directly in it.
  char *path = alloc_printf("%s/.cur_input", data->afl->out_dir);
  bool ok = read_queue_file(path, buf);
  ck_free(path);
  return ok;
}

// Pair forensics: record the admitted run's input at its (node, dir) edge.
// The first admitted run at an edge is the one that inserted the suffix (and
// possibly created the terminal edge there), so a later veto at (node, dir)
// pairs with this input: identical PCBT path, bitmap difference is what the
// tree missed.
static void record_admitted_pair(my_mutator_t *data, pcbt::NodeRef tail_node,
                                 uint8_t tail_dir) {
  if (!data->pair_log || tail_node == pcbt::kUnexplored) return;
  std::vector<u8> buf;
  if (!read_cur_input(data, &buf)) return;
  fprintf(data->pair_log, "admit node=%u cid=%u dir=%u len=%zu hex=",
          tail_node, data->tree.cid_of(tail_node), tail_dir, buf.size());
  size_t shown = buf.size() < 4096 ? buf.size() : 4096;
  for (size_t i = 0; i < shown; ++i) {
    fprintf(data->pair_log, "%02x", buf[i]);
  }
  if (shown < buf.size()) fprintf(data->pair_log, " TRUNC");
  fprintf(data->pair_log, "\n");
  fflush(data->pair_log);
}

// Veto side of the identical-PCBT-path pair forensics: a veto-probe that
// gained coverage was vetoed at (last_veto_node, last_veto_dir); the admit
// row recorded at the same (node, dir) (record_admitted_pair) is the pair
// with the identical PCBT path. Same path + different bitmap = a predicate
// node missing from the PCBT (collection incompleteness), merging two paths
// that should have forked, both landing on the same terminal.
static void record_veto_probe_pair(my_mutator_t *data, const char *fname) {
  if (!data->pair_log || data->last_veto_node == pcbt::kUnexplored) return;
  std::vector<u8> buf;
  if (!read_queue_file(fname, &buf)) return;
  fprintf(data->pair_log, "veto node=%u cid=%u dir=%u kind=%u len=%zu hex=",
          data->last_veto_node, data->tree.cid_of(data->last_veto_node),
          data->last_veto_dir, data->last_probe_veto_kind, buf.size());
  size_t shown = buf.size() < 4096 ? buf.size() : 4096;
  for (size_t i = 0; i < shown; ++i) {
    fprintf(data->pair_log, "%02x", buf[i]);
  }
  if (shown < buf.size()) fprintf(data->pair_log, " TRUNC");
  fprintf(data->pair_log, "\n");
  fflush(data->pair_log);
}

static void classify_suffix(my_mutator_t *data, uint64_t *empty,
                            uint64_t *nonempty, uint64_t *overflow,
                            uint64_t *events_sum) {
  symafl_single_pass_control *control = data->single_pass_control;
  uint32_t count = __atomic_load_n(&control->event_count, __ATOMIC_ACQUIRE);
  bool over = __atomic_load_n(&control->overflow, __ATOMIC_ACQUIRE) ||
              count > control->event_capacity;
  if (over) {
    *overflow += 1;
  } else if (count > 0) {
    *nonempty += 1;
    *events_sum += count;
  } else {
    *empty += 1;
  }
}

extern "C" void afl_custom_post_run(my_mutator_t *data) {
  // Probe diagnostic: classify what a sampled vetoed candidate executed past
  // the known terminal prefix. Nonempty suffix = screening defect (the tree
  // claimed the decision trace terminates, but it does not).
  if (data->last_was_probe && data->probe_diag && data->single_pass_armed) {
    symafl_single_pass_control *control = data->single_pass_control;
    uint32_t count = __atomic_load_n(&control->event_count, __ATOMIC_ACQUIRE);
    bool over = __atomic_load_n(&control->overflow, __ATOMIC_ACQUIRE) ||
                count > control->event_capacity;
    if (over) {
      data->diag_probe_suffix_overflow += 1;
      data->last_probe_suffix_overflow = true;
    } else if (count > 0) {
      data->diag_probe_suffix_nonempty += 1;
      data->diag_probe_suffix_events += count;
      data->last_probe_suffix_nonempty = true;
      if (data->diag_probe_details < 30) {
        data->diag_probe_details += 1;
        fprintf(stderr,
                "[pcbt-diag] probe-detail len=%u veto_depth=%u veto_node=%u "
                "suffix=%u\n",
                data->last_probe_len, data->last_veto_depth,
                data->last_veto_node, count);
        fprintf(stderr, "[pcbt-diag]   input:");
        for (uint32_t k = 0; k < data->last_probe_input_len; ++k) {
          fprintf(stderr, " %02x", data->last_probe_input[k]);
        }
        fprintf(stderr, "\n");
        if (data->tree.debug() &&
            data->last_veto_node != pcbt::kUnexplored) {
          data->tree.DebugPredicate(data->last_veto_node,
                                    data->last_probe_input,
                                    data->last_probe_len);
        }
        fprintf(stderr, "[pcbt-diag]   suffix events:");
        uint32_t shown = count < 8 ? count : 8;
        for (uint32_t k = 0; k < shown; ++k) {
          const symafl_single_pass_event &ev = control->events[k];
          fprintf(stderr, " cid=%u label=%u res=%u cnt=%u",
                  ev.cid, ev.label, ev.result, ev.count);
        }
        fprintf(stderr, "\n");
        // Label structure of the first suffix events: what do these
        // decisions actually depend on?
        if (count > 0) {
          const symafl_single_pass_event &ev = control->events[0];
          if (ev.label >= 1 && ev.label < MAX_LABEL) {
            const dfsan_label_info &li = __dfsan_label_info[ev.label];
            fprintf(stderr,
                    "[pcbt-diag]   first-suffix label_info op=%u size=%u "
                    "l1=%u l2=%u op1=%llu op2=%llu\n",
                    li.op, li.size, li.l1, li.l2,
                    (unsigned long long)li.op1.i,
                    (unsigned long long)li.op2.i);
          }
        }
      }
    } else {
      data->diag_probe_suffix_empty += 1;
    }
    if (!data->probe_capture_pending) disarm_capture(data);
    return;
  }
  if (data->bootstrap_done) {
    // Admitted-run diagnostic: does the frontier suffix carry decisions
    // (tree gain) even when the run gains no bitmap coverage?
    if (data->probe_diag && data->single_pass_armed &&
        data->last_node != pcbt::kUnexplored) {
      classify_suffix(data, &data->diag_admit_suffix_empty,
                      &data->diag_admit_suffix_nonempty,
                      &data->diag_admit_suffix_overflow,
                      &data->diag_admit_suffix_events);
    }
    // The tree learns an admitted run's suffix ONLY when the run gains
    // coverage (afl_custom_queue_new_entry inserts it). A non-gaining run
    // contributes nothing to the tree: post_process's retry bookkeeping
    // bumps rCnt for its frontier edge, so rlimit bounds how many times a
    // frontier edge is re-mined before candidates there are vetoed
    // (veto_rlimit). This block deliberately does NOT reset last_node
    // (post_process needs it for the rCnt bump) and does NOT consume the
    // capture: queue_new_entry reads it for the gaining run, and
    // post_process disarms it when no gain happened.
    return;
  }
  if (!data->single_pass_armed) return;
  uint32_t mode = __atomic_load_n(&data->single_pass_control->mode,
                                  __ATOMIC_ACQUIRE);
  pcbt::NodeRef tail_node = pcbt::kUnexplored;
  uint8_t tail_dir = 0;
  if (mode == SYMAFL_TRACE_SUFFIX_SHM &&
      data->last_node != pcbt::kUnexplored) {
    (void)insert_suffix_capture(data, nullptr, 0, "bootstrap", &tail_node,
                                &tail_dir);
  } else if (mode == SYMAFL_TRACE_FULL_STREAM) {
    std::vector<u8> buf;
    if (read_cur_input(data, &buf)) {
      (void)insert_full_stream(data, buf.data(), buf.size(), "bootstrap",
                               &tail_node, &tail_dir);
    } else {
      fprintf(stderr, "[pcbt] bootstrap cur_input unreadable (out_dir=%s); "
              "replay with len=0\n",
              data->afl->out_dir ? (const char *)data->afl->out_dir
                                 : "(null)");
      (void)insert_full_stream(data, nullptr, 0, "bootstrap", &tail_node,
                               &tail_dir);
    }
  }
  // The bootstrap admit that created a terminal edge is the pair partner
  // for later veto-but-gain probes on that edge; record it too (the empty
  // tree case has last_node == kUnexplored and is skipped by the guard).
  record_admitted_pair(data, tail_node, tail_dir);
  data->last_node = pcbt::kUnexplored;
}

extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  (void)filename;
  data->bootstrap_done = true;
  if (data->concolic_deadline && !data->phase_start) {
    data->phase_start = time(nullptr);
  }
  return 1;
}

extern "C" u8 afl_custom_queue_new_entry(my_mutator_t *data,
                                         const u8 *filename_new_queue,
                                         const u8 *filename_orig_queue) {
  (void)filename_orig_queue;
  // A veto-probe that gained coverage. Only an rlimit probe has a still-open
  // frontier, so only that class may feed InsertSuffix. Terminal probe gains
  // remain diagnostics; reopening a terminal would violate the tree contract.
  if (data->last_was_probe) {
    data->last_was_probe = false;
    data->veto_probe_gained += 1;
    if (data->last_probe_veto_kind == 0)
      data->probe_gained_terminal += 1;
    else
      data->probe_gained_rlimit += 1;
    if (data->probe_gained_log) {
      fprintf(data->probe_gained_log, "kind=%u node=%u dir=%u %s\n",
              data->last_probe_veto_kind, data->last_veto_node,
              data->last_veto_dir, filename_new_queue);
      fflush(data->probe_gained_log);
    }
    record_veto_probe_pair(data, (const char *)filename_new_queue);

    bool learned = false;
    if (data->probe_learn && data->last_probe_veto_kind == 1 &&
        data->probe_capture_pending &&
        data->probe_capture_node != pcbt::kUnexplored) {
      std::vector<u8> buf;
      const bool have_input = read_queue_file(
          (const char *)filename_new_queue, &buf);
      const pcbt::NodeRef node = data->probe_capture_node;
      const uint8_t dir = data->probe_capture_dir;
      if (have_input && data->single_pass_armed) {
        data->last_node = node;
        data->last_dir = dir;
        uint32_t mode = __atomic_load_n(&data->single_pass_control->mode,
                                        __ATOMIC_ACQUIRE);
        pcbt::NodeRef tail_node = pcbt::kUnexplored;
        uint8_t tail_dir = 0;
        learned = mode == SYMAFL_TRACE_SUFFIX_SHM
            ? insert_suffix_capture(data, buf.data(), buf.size(),
                                    (const char *)filename_new_queue,
                                    &tail_node, &tail_dir)
            : mode == SYMAFL_TRACE_SUFFIX_PIPE
                  ? insert_pipe_suffix_capture(
                        data, buf.data(), buf.size(),
                        (const char *)filename_new_queue, &tail_node, &tail_dir)
                  : false;
        // SHM overflow is a confirmed coverage gain, so replay the same bytes
        // with pipe-suffix using the same frontier before giving up.
        if (!learned && !data->single_pass_armed) {
          learned = replay_pipe_suffix(data, buf.data(), buf.size(),
                                       (const char *)filename_new_queue,
                                       node, dir);
        }
      }
      data->last_node = pcbt::kUnexplored;
      data->probe_capture_pending = false;
      data->probe_capture_node = pcbt::kUnexplored;
      if (learned) data->probe_learned += 1;
      else data->probe_learn_failed += 1;
    }
    if (!data->probe_capture_pending && data->single_pass_armed)
      disarm_capture(data);
    if (data->sat_window) data->sat_probe_gained += 1;
    if (data->probe_diag) {
      if (data->last_probe_suffix_nonempty) data->probe_gained_nonempty += 1;
      else if (data->last_probe_suffix_overflow) data->probe_gained_overflow += 1;
      else data->probe_gained_empty += 1;
      // Capture real vetoed-gainful cases for event-free divergence
      // forensics: the queue file holds the input, the veto position
      // identifies where the tree claimed termination, and the suffix class
      // tells whether the real decision trace continued past it.
      fprintf(stderr,
              "[pcbt-diag] gained-case probe file=%s len=%u veto_depth=%u "
              "veto_node=%u veto_cid=%u veto_dir=%u veto_kind=%u suffix=%s\n",
              filename_new_queue, data->last_probe_input_len,
              data->last_veto_depth, data->last_veto_node,
              data->last_veto_node != pcbt::kUnexplored
                  ? data->tree.cid_of(data->last_veto_node)
                  : 0u,
              data->last_veto_dir, data->last_probe_veto_kind,
              data->last_probe_suffix_nonempty
                  ? "nonempty"
                  : data->last_probe_suffix_overflow ? "overflow" : "empty");
    }
    data->last_probe_suffix_overflow = false;
    data->last_gained = true;
    return 0;
  }
  // Seeds and post-saturation concrete-phase gains are not PCBT admissions.
  if (!data->bootstrap_done || !data->screening) return 0;
  data->traced_entries.insert((const char *)filename_new_queue);
  // This admitted run gained coverage, so its suffix is tree material:
  // post_run inserts nothing (non-gaining runs only bump rCnt), and the
  // run's SHM capture is still armed for us to consume here.
  if (!data->single_pass_armed) return 0;
  const char *fname = (const char *)filename_new_queue;
  std::vector<u8> buf;
  if (!read_queue_file(fname, &buf)) {
    WARNF("cannot read coverage-gaining queue entry %s\n", fname);
    disarm_capture(data);
    return 0;
  }
  uint32_t mode = __atomic_load_n(&data->single_pass_control->mode,
                                  __ATOMIC_ACQUIRE);
  pcbt::NodeRef node = data->last_node;
  bool root_capture = data->root_shm_capture;
  uint8_t dir = data->last_dir;
  pcbt::NodeRef tail_node = pcbt::kUnexplored;
  uint8_t tail_dir = 0;
  bool inserted = mode == SYMAFL_TRACE_SUFFIX_SHM
      ? insert_suffix_capture(data, buf.data(), buf.size(), fname,
                              &tail_node, &tail_dir)
      : mode == SYMAFL_TRACE_SUFFIX_PIPE
            ? insert_pipe_suffix_capture(data, buf.data(), buf.size(), fname,
                                         &tail_node, &tail_dir)
            : mode == SYMAFL_TRACE_FULL_STREAM
                  ? insert_full_stream(data, buf.data(), buf.size(), fname,
                                       &tail_node, &tail_dir)
                  : false;
  if (inserted) record_admitted_pair(data, tail_node, tail_dir);
  if (!inserted && root_capture) {
    (void)replay_full_capture(data, buf.data(), buf.size(), fname);
  } else if (!inserted && node != pcbt::kUnexplored) {
    (void)replay_pipe_suffix(data, buf.data(), buf.size(), fname, node, dir);
  }
  data->last_gained = true;
  return 0;
}

/// PCBT screening: veto mutated candidates that cannot reach an unexplored
/// frontier. Returning 0 with *out_buf=NULL tells AFL++ to skip executing
/// this candidate entirely.
extern "C" size_t afl_custom_post_process(my_mutator_t *data, u8 *buf,
                                          size_t buf_size, u8 **out_buf) {
  // A probe capture is consumed by queue_new_entry only when AFL reports a
  // coverage gain. A non-gaining probe reaches this next callback with no
  // queue entry, so discard its suffix before screening the next candidate.
  if (data->probe_capture_pending) {
    if (data->single_pass_armed) disarm_capture(data);
    data->probe_capture_pending = false;
    data->probe_capture_node = pcbt::kUnexplored;
  }
  // Clear the veto-probe marker for every new candidate; it is only true
  // between a probe admission and that probe's own coverage outcome.
  data->last_was_probe = false;
  // rCnt bookkeeping for the previously admitted candidate
  if (data->last_node != pcbt::kUnexplored) {
    if (!data->last_gained) {
      uint8_t &count = data->tree.retry_count(data->last_node, data->last_dir);
      if (count != UINT8_MAX) count += 1;
    }
    if (data->single_pass_armed) {
      disarm_capture(data);
    }
    data->last_node = pcbt::kUnexplored;
  }

  // Hard deadline: reproducible concolic-phase length. Evaluated on EVERY
  // post_process call (not just the non-probe veto path - probe-every=1
  // returns before the old position, which made the deadline unreachable).
  // phase_start is initialized on the first check (queue_get may not run
  // before the first screened candidate), so a deadline of N means N seconds
  // after screening begins.
  if (data->concolic_deadline && !data->saturation_logged) {
    time_t now = time(nullptr);
    if (data->phase_start == 0) {
      data->phase_start = now;
    } else if ((uint64_t)(now - data->phase_start) >=
               data->concolic_deadline) {
      data->saturation_logged = true;
      print_concolic_phase_snapshot(data);
      fprintf(stderr,
              "[pcbt] concolic phase deadline (%llus) reached; "
              "switching to concrete\n",
              (unsigned long long)data->concolic_deadline);
      data->screening = false;
      data->afl->pcbt_switch_pending = 1;
    }
  }

  if (!data->screening) {
    data->screened += 1;
    data->admitted += 1;
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  data->screened += 1;
  pcbt::NodeRef node = pcbt::kUnexplored;
  uint8_t dir = 0;
  if (check_input_timed(data, buf, (uint32_t)buf_size, &node, &dir,
                        &data->last_veto_depth, &data->last_veto_node,
                        &data->last_veto_dir, &data->last_veto_kind)) {
    data->admitted += 1;
    data->vetoes_since_admit = 0;
    data->last_gained = false;
    // Dry-run corpus paths must all enter the tree, so bootstrap is always
    // pipe-full. Thereafter a candidate at an established frontier uses SHM
    // suffix capture. An opaque/evaluation-failure admission has no frontier,
    // so it uses a root SHM stream and only falls back to full-pipe replay if
    // AFL++ confirms a gain after that bounded capture overflows. The pipe is
    // therefore reserved for bootstrap and confirmed overflow replays.
    // When replay_check is enabled, always use full-pipe so the complete
    // trace can be compared against the current tree before insertion.
    if (!data->bootstrap_done || data->replay_check) {
      data->last_node = node;
      data->last_dir = dir;
      arm_full_capture(data);
    } else if (node == pcbt::kUnexplored && data->root_shm_enabled) {
      arm_root_shm_capture(data);
    } else if (node == pcbt::kUnexplored) {
      data->last_node = node;
      data->last_dir = dir;
      arm_full_capture(data);
    } else {
      arm_suffix_capture(data, node, dir);
    }
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  data->vetoed += 1;
  ++data->vetoes_since_admit;
  write_progress(data, false);
  if (data->probe_diag) {
    // Veto depth histogram (16-deep buckets; >=256 in the last).
    uint32_t d = data->last_veto_depth;
    size_t b = d / 16;
    if (b > 16) b = 16;
    data->diag_veto_depth[b] += 1;
  }
  // Veto probe: execute a sampled vetoed candidate to measure whether the
  // screening is incorrectly vetoing would-be coverage-gaining inputs. The
  // probe does not arm capture, so it never grows the tree; its coverage gain
  // (if any) is counted in veto_probe_gained. With SYMAFL_PROBE_DIAG it arms
  // suffix capture at the veto depth so post_run can classify the suffix.
  if (data->veto_probe_every &&
      ++data->veto_probe_count >= data->veto_probe_every) {
    data->veto_probe_count = 0;
    data->veto_probe_admitted += 1;
    data->last_was_probe = true;
    data->last_gained = false;
    data->last_node = pcbt::kUnexplored;
    data->last_probe_veto_kind = data->last_veto_kind;
    data->last_probe_suffix_nonempty = false;
    data->last_probe_len = (uint32_t)buf_size;
    data->last_probe_input_len = (uint32_t)buf_size < 64 ? (uint32_t)buf_size : 64;
    memcpy(data->last_probe_input, buf, data->last_probe_input_len);
    if (data->sat_window) data->sat_probe_total += 1;
    if (data->single_pass_armed) disarm_capture(data);
    if (data->probe_diag && data->last_veto_depth > 0) {
      arm_suffix_capture(data, data->last_veto_node, data->last_veto_dir);
      data->probe_capture_pending = data->probe_learn &&
                                    data->last_probe_veto_kind == 1;
      data->probe_capture_node = data->last_veto_node;
      data->probe_capture_dir = data->last_veto_dir;
      // Probe capture is not an admitted candidate: do not let the normal
      // post_run retry bookkeeping treat it as last_node/last_dir.
      data->last_node = pcbt::kUnexplored;
    } else if (data->probe_learn && data->last_probe_veto_kind == 1 &&
               data->last_veto_depth > 0) {
      arm_suffix_capture(data, data->last_veto_node, data->last_veto_dir);
      data->probe_capture_pending = true;
      data->probe_capture_node = data->last_veto_node;
      data->probe_capture_dir = data->last_veto_dir;
      data->last_node = pcbt::kUnexplored;
    }
    *out_buf = buf;
    return buf_size;
  }
  // Probe-gain saturation: the vetoed population stopped paying out.
  if (data->sat_window && data->sat_probe_total >= data->sat_window) {
    bool sat = data->sat_probe_gained < data->sat_min_gains;
    if (!data->saturation_logged) {
      fprintf(stderr,
              "[pcbt] sat window: probes=%llu gains=%llu min=%llu -> %s\n",
              (unsigned long long)data->sat_probe_total,
              (unsigned long long)data->sat_probe_gained,
              (unsigned long long)data->sat_min_gains,
              sat ? "saturated" : "unsaturated");
    }
    data->sat_probe_total = 0;
    data->sat_probe_gained = 0;
    data->sat_low_windows = sat ? data->sat_low_windows + 1 : 0;
    if (sat && data->sat_low_windows >= data->sat_consec) {
      if (!data->saturation_logged) {
        data->saturation_logged = true;
        print_concolic_phase_snapshot(data);
        fprintf(stderr,
                "[pcbt] probe-gain saturation after %llu vetoes "
                "(window=%llu gains=%llu consec=%llu phase_secs=%llu); "
                "switching to concrete\n",
                (unsigned long long)data->vetoed,
                (unsigned long long)data->sat_window,
                (unsigned long long)data->sat_min_gains,
                (unsigned long long)data->sat_low_windows,
                data->phase_start
                    ? (unsigned long long)(time(nullptr) - data->phase_start)
                    : 0ull);
      }
      data->screening = false;
      data->afl->pcbt_switch_pending = 1;
    }
  }
  // A saturated PCBT is a phase boundary, not a local screening fallback.
  // Let AFL++ perform the restart at its next scheduler boundary, where it
  // can safely replace the forkserver and rebuild its coverage state.
  if (data->tree.IsSaturated(data->rlimit)) {
    data->screening = false;
    data->afl->pcbt_switch_pending = 1;
    if (!data->saturation_logged) {
      data->saturation_logged = true;
      fprintf(stderr,
              "[pcbt] tree saturated after %llu vetoes "
              "(phase_secs=%llu); switching to concrete\n",
              (unsigned long long)data->vetoed,
              data->phase_start
                  ? (unsigned long long)(time(nullptr) - data->phase_start)
                  : 0ull);
    }
  }
  *out_buf = NULL;
  return 0;
}

extern "C" const char *afl_custom_introspection(my_mutator_t *data) {
  static char buf[2048];
  const pcbt::Tree &t = data->tree;
  snprintf(buf, sizeof(buf),
           "traces=%llu nodes=%llu pred_nodes=%llu depth=%llu conflicts=%llu opaque=%llu "
           "failed=%llu timeouts=%llu memerr=%llu "
           "screened=%llu admitted=%llu vetoed=%llu traced_entries=%llu saturated=%llu "
           "single_pass=%llu single_pass_overflow=%llu "
           "admit_empty=%llu admit_opaque=%llu admit_eval_failure=%llu admit_frontier=%llu "
           "admit_len_veto=%llu veto_terminal=%llu veto_rlimit=%llu probe_admitted=%llu probe_gained=%llu "
           "probe_gained_terminal=%llu probe_gained_rlimit=%llu profile=%d "
           "check_ns=%llu check_calls=%llu trace_ns=%llu trace_calls=%llu "
           "replay_ns=%llu replay_calls=%llu",
           (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
           (unsigned long long)t.num_pred_nodes(),
           (unsigned long long)t.max_depth,
           (unsigned long long)t.num_conflicts,
           (unsigned long long)t.num_opaque,
           (unsigned long long)data->failed_runs,
           (unsigned long long)data->trace_timeouts,
           (unsigned long long)data->memerr_events,
           (unsigned long long)data->screened,
           (unsigned long long)data->admitted,
           (unsigned long long)data->vetoed,
           (unsigned long long)data->traced_entries.size(),
           (unsigned long long)(data->screening ? 0 : 1),
           (unsigned long long)data->single_pass_captures,
           (unsigned long long)data->single_pass_overflows,
           (unsigned long long)t.check_admit_empty,
           (unsigned long long)t.check_admit_opaque,
           (unsigned long long)t.check_admit_eval_failure,
           (unsigned long long)t.check_admit_frontier,
           (unsigned long long)t.check_admit_len_veto,
           (unsigned long long)t.check_veto_terminal,
           (unsigned long long)t.check_veto_rlimit,
           (unsigned long long)data->veto_probe_admitted,
           (unsigned long long)data->veto_probe_gained,
           (unsigned long long)data->probe_gained_terminal,
           (unsigned long long)data->probe_gained_rlimit,
           (int)(data->profile_enabled ? 1 : 0),
           (unsigned long long)data->profile_check_ns,
           (unsigned long long)data->profile_check_calls,
           (unsigned long long)data->profile_trace_ns,
           (unsigned long long)data->profile_trace_calls,
           (unsigned long long)data->profile_replay_ns,
           (unsigned long long)data->profile_replay_calls);
  return buf;
}
