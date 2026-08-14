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
#include "worker_client.hpp"

extern "C" {
#include "afl-fuzz.h"
}

#include <algorithm>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <spawn.h>
#include <signal.h>

extern char **environ;

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
    if (concolic_target) {
      ck_free(concolic_target);
      concolic_target = nullptr;
    }
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
    worker_close(&worker);
    if (probe_case_dir) ck_free(probe_case_dir);
    if (probe_terminal_dir) ck_free(probe_terminal_dir);
    if (probe_rlimit_dir) ck_free(probe_rlimit_dir);
    if (forensics_dir) ck_free(forensics_dir);
    if (anomaly_case_dir) ck_free(anomaly_case_dir);
    if (anomaly_index) {
      fclose(anomaly_index);
      anomaly_index = nullptr;
    }
    if (pair_log_path) ck_free(pair_log_path);
  }

  afl_state_t *afl;

  // Probe inputs are retained for diagnosis, but never under AFL's queue.
  char *probe_case_dir = nullptr;
  char *probe_terminal_dir = nullptr;
  char *probe_rlimit_dir = nullptr;
  uint64_t probe_case_seq = 0;

  pcbt::Tree tree;
  std::unordered_set<std::string> traced_entries;
  bool bootstrap_done = false;

  // screening gates the concolic stage (bootstrap flush + gain-gated insert).
  // veto_enabled gates CheckInput; production default is off (ADR 0009).
  bool screening = true;
  bool veto_enabled = false;
  uint8_t rlimit = 16;
  uint8_t len_rlimit = 16;
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
  // SYMAFL_REPLAY_ALL=1: replay EVERY admitted run's full stream against the
  // tree (including non-gaining runs), not only coverage-gaining runs.
  bool replay_all = false;
  // Quality contract: on first hard residual counter bump, stop_soon + marker
  // so the instance keeps forensics and exits into RCA (no further testing).
  // Default on with REPLAY_ALL; override with SYMAFL_ABORT_ON_RESIDUAL=0/1.
  bool abort_on_residual = false;
  bool residual_abort_fired = false;
  // Set by post_run after it replayed the current run; consumed by
  // queue_new_entry's insert so a gaining run is not replayed twice.
  bool replay_run_done = false;
  uint64_t replay_checked = 0;
  uint64_t replay_cid_mismatch = 0;
  uint64_t replay_direction_mismatch = 0;
  uint64_t replay_after_terminal = 0;
  uint64_t replay_truncated = 0;
  uint64_t replay_timeout_skipped = 0;
  // Non-timeout signal death (e.g. SIGSEGV): incomplete stream by construction,
  // same isolation class as timeout_skipped — not entry_artifact / truncated.
  uint64_t replay_crash_skipped = 0;
  // TruncatedTrace where a direct re-exec of the same input produces a longer
  // stream that continues past the in-AFL capture (or diverges). Isolates
  // incomplete forkserver captures from true decision-omission pure-prefix.
  uint64_t replay_short_capture_skipped = 0;
  char *concolic_target = nullptr;
  // Three-fsrv pipeline: the main forkserver runs the concrete target; the
  // concolic and sanitizer forkservers are spawned by AFL++ at startup. The
  // sanitizer target is optional (SYMAFL_SANITIZER_TARGET).
  char *sanitizer_target = nullptr;
  // Init-time queue_new_entry batch: read_testcases runs before the concolic
  // forkserver exists, so seed entries are queued here and flushed at the
  // first afl_custom_queue_get (before any post_process).
  std::vector<std::string> pending_seeds;
  bool seeds_flushed = false;
  bool worker_mode = false;
  WorkerClient worker;
  std::unordered_map<std::string, std::vector<pcbt::AttachedClosure>>
      closures_by_file;
  std::vector<pcbt::AttachedClosure> current_closures;
  std::vector<u8> focused_scratch;
  uint32_t focused_rr = 0;
  uint64_t focused_rng = 1;
  uint64_t focused_tried = 0;
  uint64_t focused_screened = 0;
  uint64_t focused_exec = 0;
  // Pipeline accounting: concolic runs are executed only for coverage-gaining
  // admitted candidates (production) plus every admitted candidate under
  // REPLAY_ALL / probe_diag measurement modes.
  uint64_t concolic_run_calls = 0;
  uint64_t concolic_run_failed = 0;
  uint64_t san_run_calls = 0;
  uint64_t san_tmouts = 0;
  uint64_t san_crashes = 0;          // sanitizer crash events (all)
  uint64_t san_crashes_saved = 0;    // crash files written
  std::unordered_map<int, uint64_t> san_crash_sig_counts;  // per-signal dedup
  uint64_t san_crash_seq = 0;        // monotonic id for saved crashes
  // Full-stream capture artifacts: empty event list (taint/capture not armed)
  // or first event is not the entry constraint. Counted separately from
  // truncated decision-omission so hard-gate zeroing is not poisoned by
  // transport defects (see aeda20e entry-fork guard).
  uint64_t replay_entry_artifact = 0;
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
  uint64_t profile_exec_ns = 0;      // forkserver target execution wall time
  uint64_t profile_exec_calls = 0;
  bool profile_exec_armed = false;   // current post_process admits a concolic run

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
  uint8_t last_veto_kind = 0;         // 0=terminal, 1=rlimit, 2=unstable
  uint8_t last_probe_veto_kind = 0;   // veto kind of the last probe candidate
  uint8_t last_probe_input[64] = {};
  uint32_t last_probe_input_len = 0;

  // Immediate forensic snapshots.  The first few instances of each hard
  // diagnostic are persisted from the current child/table before either is
  // reused; later instances remain counters so diagnostics cannot dominate
  // throughput.
  char *forensics_dir = nullptr;
  uint64_t forensic_limit = 8;
  uint64_t forensic_seq = 0;
  uint64_t forensic_opaque_seen = 0;
  uint64_t forensic_opaque_captured = 0;
  uint64_t forensic_opaque_suppressed = 0;
  uint64_t forensic_terminal_seen = 0;
  uint64_t forensic_terminal_captured = 0;
  uint64_t forensic_terminal_suppressed = 0;
  uint64_t forensic_struct_seen = 0;
  uint64_t forensic_struct_captured = 0;
  uint64_t forensic_struct_suppressed = 0;
  // Transport / hard-replay anomaly cases (entry_artifact, cid/dir/afterT/trunc).
  // These must always dump the candidate input when a forensics dir or out_dir
  // is available — without the bytes the counter is not actionable.
  uint64_t forensic_entry_seen = 0;
  uint64_t forensic_entry_captured = 0;
  uint64_t forensic_entry_suppressed = 0;
  uint64_t forensic_replay_seen = 0;
  uint64_t forensic_replay_captured = 0;
  uint64_t forensic_replay_suppressed = 0;
  // Append-only index under forensics_dir (or <out_dir>/anomaly-cases).
  FILE *anomaly_index = nullptr;
  char *anomaly_case_dir = nullptr;
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
  char *pair_log_path = nullptr;
  // SYMAFL_PROBE_GAINED_LOG: append-only list of queue filenames that were
  // vetoed, probe-executed, and gained coverage. Used for end-of-run bitmap
  // checks: does the gain survive to the final bitmap, or was it superseded?
  FILE *probe_gained_log = nullptr;
  // SYMAFL_ADMITTED_GAINED_LOG records PCBT admissions that created an AFL
  // queue entry. Together with the veto-probe log it permits exact terminal
  // bitmap accounting without treating seed or post-switch entries as PCBT
  // admissions.
  FILE *admitted_gained_log = nullptr;
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
                                        veto_dir, veto_kind,
                                        data->len_rlimit);
  profile_stop(data, start, &data->profile_check_ns,
               &data->profile_check_calls);
  return admitted;
}

// AFL++ measures exactly around afl_fsrv_run_target() and reports the result
// here. Only an admitted concolic candidate arms this counter; veto probes and
// post-saturation concrete executions are excluded from exec/s.
extern "C" void afl_custom_exec_time(my_mutator_t *data,
                                      uint64_t elapsed_ns) {
  if (!data->profile_exec_armed) return;
  data->profile_exec_ns += elapsed_ns;
  data->profile_exec_calls += 1;
  data->profile_exec_armed = false;
}

static void print_concolic_phase_snapshot(const my_mutator_t *data) {
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt-concolic-phase] screened=%llu admitted=%llu "
          "vetoed=%llu traced_entries=%llu probe_admitted=%llu "
          "probe_gained=%llu admit_frontier=%llu admit_len_veto=%llu "
          "veto_terminal=%llu veto_rlimit=%llu veto_unstable=%llu "
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
          (unsigned long long)t.check_veto_unstable,
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
  // Grow the kernel pipe buffer so a REPLAY_ALL full stream (tens of KiB of
  // cond frames) does not block the child if the parent is briefly busy. A
  // blocked child under -t 2000 is SIGKILL'd and looks like a short capture.
#ifdef F_SETPIPE_SZ
  {
    const int want = 1 << 20;  // 1 MiB
    (void)fcntl(pipefd[0], F_SETPIPE_SZ, want);
    (void)fcntl(pipefd[1], F_SETPIPE_SZ, want);
  }
#endif
  // The trace pipe belongs to the concolic forkserver: only its children
  // carry the SymAFL runtime that writes condition frames. The main
  // (concrete) forkserver never writes to it and must keep sym_trace_fd = -1
  // so its runs do not drain into the wrong buffer.
  data->afl->fsrv_concolic.sym_trace_fd = data->full_stream_read_fd;

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
  my_mutator_t *data = new my_mutator_t(afl);
  if (!data) {
    FATAL("afl_custom_init alloc");
    return NULL;
  }
  data->focused_rng = seed ? seed : 1u;

  // Three-fsrv pipeline: the CLI target is the concrete binary (drives the
  // main loop and coverage feedback); SYMAFL_CONCOLIC_TARGET names the
  // concolic forkserver binary (run only on coverage-gaining admissions) and
  // SYMAFL_SANITIZER_TARGET (optional) the sanitizer forkserver binary (run
  // after the concolic stage on the same gaining candidates). AFL++ spawns
  // both secondary forkservers at startup after this init returns.
  const char *concolic = getenv("SYMAFL_CONCOLIC_TARGET");
  if (!concolic || !*concolic) {
    FATAL("PCBT mode requires SYMAFL_CONCOLIC_TARGET (CLI target is the "
          "concrete binary)");
  }
  if (access(concolic, X_OK)) {
    PFATAL("PCBT concolic target is not executable");
  }
  const char *san = getenv("SYMAFL_SANITIZER_TARGET");
  if (san && *san && access(san, X_OK)) {
    PFATAL("PCBT sanitizer target is not executable");
  }
  data->afl->pcbt_mode = 1;
  data->concolic_target = (char *)ck_strdup((u8 *)concolic);
  if (san && *san) data->sanitizer_target = (char *)ck_strdup((u8 *)san);

  if (const char *mode = getenv("SYMAFL_TRACE_MODE")) {
    WARNF("SYMAFL_TRACE_MODE=%s is ignored: PCBT transport is selected "
          "by lifecycle (bootstrap=pipe-full, steady=shm-suffix, "
          "overflow+gain=pipe-suffix)\n", mode);
  }
  if (const char *wsock = getenv("SYMAFL_WORKER_SOCK")) {
    data->worker_mode = true;
    if (!worker_connect(&data->worker, wsock)) {
      FATAL("SYMAFL_WORKER_SOCK connect failed: %s", wsock);
    }
    fprintf(stderr, "[pcbt] worker client connected (%s)\n", wsock);
  } else {
    init_forkserver_capture(data);
  }

  if (const char *forensics = getenv("SYMAFL_FORENSICS_DIR")) {
    if (!*forensics) FATAL("SYMAFL_FORENSICS_DIR must not be empty");
    data->forensics_dir = (char *)ck_strdup((u8 *)forensics);
    if (mkdir(data->forensics_dir, 0755) && errno != EEXIST) {
      PFATAL("cannot create SYMAFL forensic directory %s",
             data->forensics_dir);
    }
    if (const char *limit = getenv("SYMAFL_FORENSICS_LIMIT")) {
      char *end = nullptr;
      unsigned long long parsed = strtoull(limit, &end, 10);
      if (end == limit || *end != '\0' || parsed == 0) {
        FATAL("Invalid SYMAFL_FORENSICS_LIMIT=%s", limit);
      }
      data->forensic_limit = parsed;
    }
    fprintf(stderr, "[pcbt] immediate forensics: %s (limit=%llu per reason)\n",
            data->forensics_dir,
            (unsigned long long)data->forensic_limit);
  }
  // Hard-anomaly case dump (entry_artifact, cid/dir/afterT/trunc). Prefer
  // SYMAFL_FORENSICS_DIR/anomaly-cases; otherwise <out_dir>/anomaly-cases so
  // REPLAY_ALL runs never lose the offending input.
  {
    char *case_dir = nullptr;
    if (data->forensics_dir) {
      case_dir = alloc_printf("%s/anomaly-cases", data->forensics_dir);
    } else if (afl->out_dir && *afl->out_dir) {
      case_dir = alloc_printf("%s/anomaly-cases", afl->out_dir);
    }
    if (case_dir) {
      if (mkdir(case_dir, 0755) && errno != EEXIST) {
        WARNF("cannot create anomaly case directory %s: %s\n", case_dir,
              strerror(errno));
        ck_free(case_dir);
      } else {
        data->anomaly_case_dir = case_dir;
        // Pair RCA: retain first-creating input per tree node so cid/dir
        // mismatch dumps include ADMIT as well as PROBE.
        data->tree.set_store_creators(true, /*max_len=*/65536);
        char *index_path =
            alloc_printf("%s/index.tsv", data->anomaly_case_dir);
        data->anomaly_index = fopen(index_path, "a");
        if (data->anomaly_index) {
          // Header only when the file is empty (first open of a new run).
          if (ftell(data->anomaly_index) == 0) {
            fprintf(data->anomaly_index,
                    "seq\treason\tinput_len\tpipe_bytes\tevents\t"
                    "first_cid\tfirst_constraint\tkill_sig\ttimeout\t"
                    "mode\tentry_cid\tentry_constraint\tpath\t"
                    "admit_found\tadmit_len\tmismatch_node\n");
            fflush(data->anomaly_index);
          }
        }
        ck_free(index_path);
        fprintf(stderr,
                "[pcbt] anomaly case dump: %s (entry/replay hard faults "
                "save probe+admit pair: input/pipe/events)\n",
                data->anomaly_case_dir);
      }
    }
  }

  if (getenv("SYMAFL_REPLAY_CHECK")) {
    data->replay_check = true;
    fprintf(stderr, "[pcbt] replay check enabled: all admitted candidates "
            "use full-pipe capture and trace replay validation\n");
  }
  if (getenv("SYMAFL_REPLAY_ALL")) {
    data->replay_all = true;
    data->replay_check = true;
    fprintf(stderr, "[pcbt] replay-all enabled: EVERY admitted run (gaining "
            "and non-gaining) is full-pipe captured and replayed against "
            "the tree; mismatches mark nodes unstable and are counted\n");
  }
  // Abort-on-residual: default ON when REPLAY_ALL (quality/RQ1). First hard
  // residual stops the instance immediately so logs/forensics are retained and
  // the agent enters RCA instead of burning the rest of MIN_SCREENED/1e6.
  {
    const char *aor = getenv("SYMAFL_ABORT_ON_RESIDUAL");
    if (aor && aor[0] == '0' && aor[1] == '\0') {
      data->abort_on_residual = false;
    } else if (aor && aor[0] == '1' && aor[1] == '\0') {
      data->abort_on_residual = true;
    } else {
      data->abort_on_residual = data->replay_all || data->replay_check;
    }
    if (data->abort_on_residual) {
      fprintf(stderr,
              "[pcbt] abort-on-residual: first hard residual sets stop_soon "
              "and writes ABORT_RESIDUAL (quality contract)\n");
    }
  }
  // rlimit-unlimited quality mode: bypass the rCnt/rlimit budget so every
  // candidate that reaches an unexplored edge is admitted. Setting rlimit to
  // 255 is NOT equivalent - a hot edge still exhausts 255 retries and starts
  // rlimit-vetoing candidates, which would mask their streams. Replay-all
  // implies this mode: the whole point of the census is that no candidate is
  // screened out by a retry budget.
  if (getenv("SYMAFL_RCNT_UNLIMITED") || data->replay_all) {
    data->tree.set_rlimit_unlimited(true);
    fprintf(stderr, "[pcbt] rlimit unlimited: every frontier admission is "
            "granted (rCnt bypassed); saturation decided by terminal closure "
            "alone\n");
  }
  data->veto_enabled = false;
  if (const char *veto = getenv("SYMAFL_VETO")) {
    data->veto_enabled = strcmp(veto, "0") != 0 && veto[0] != '\0';
  }
  if (getenv("SYMAFL_NO_VETO")) {
    data->veto_enabled = false;
  }
  if (data->veto_enabled) {
    fprintf(stderr,
            "[pcbt] veto: CheckInput + suffix capture (SYMAFL_VETO=1)\n");
  } else {
    fprintf(stderr,
            "[pcbt] no-veto: CheckInput skipped; full-stream capture; "
            "concolic stage still runs on coverage gainers "
            "(SYMAFL_NO_SCREEN still disables learning)\n");
  }
  if (getenv("SYMAFL_NO_SCREEN")) {
    data->screening = false;
    if (!data->veto_enabled) {
      fprintf(stderr,
              "[pcbt] SYMAFL_NO_SCREEN wins over no-veto: "
              "no capture, no concolic insert\n");
    }
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
  if (getenv("SYMAFL_CONFLICT_DIAG")) {
    data->tree.set_conflict_diag(true);
    fprintf(stderr, "[pcbt] conflict-site diagnostics enabled "
            "(SYMAFL_CONFLICT_DIAG=1)\n");
  }
  if (const char *rl = getenv("SYMAFL_RCNT_LIMIT")) {
    char *end = nullptr;
    unsigned long parsed = strtoul(rl, &end, 10);
    if (end == rl || *end != '\0' || parsed > UINT8_MAX) {
      FATAL("Invalid SYMAFL_RCNT_LIMIT=%s (expected 0..255)", rl);
    }
    data->rlimit = (uint8_t)parsed;
  }
  data->len_rlimit = data->rlimit;
  if (const char *lrl = getenv("SYMAFL_LEN_RCNT_LIMIT")) {
    char *end = nullptr;
    unsigned long parsed = strtoul(lrl, &end, 10);
    if (end == lrl || *end != '\0' || parsed > UINT8_MAX) {
      FATAL("Invalid SYMAFL_LEN_RCNT_LIMIT=%s (expected 0..255)", lrl);
    }
    data->len_rlimit = (uint8_t)parsed;
  }
  fprintf(stderr, "[pcbt] retry limits: base=%u len_constraint=%u\n",
          (unsigned)data->rlimit, (unsigned)data->len_rlimit);
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
  // Probe-case persistence is needed for sampled veto probes (above) and for
  // replay-all veto forensics (every vetoed candidate is executed and
  // replayed; its input is saved so truncated/empty-stream cases can be
  // replayed outside AFL and compared with the in-run capture).
  if (data->veto_probe_every || data->replay_all) {
    const char *probe_dir = getenv("SYMAFL_PROBE_CASE_DIR");
    data->probe_case_dir = probe_dir && *probe_dir
        ? (char *)ck_strdup((u8 *)probe_dir)
        : alloc_printf("%s/probes", data->afl->out_dir);
    if (mkdir(data->probe_case_dir, 0755) && errno != EEXIST) {
      PFATAL("cannot create SYMAFL probe case directory %s",
             data->probe_case_dir);
    }
    data->probe_terminal_dir = alloc_printf("%s/terminal", data->probe_case_dir);
    data->probe_rlimit_dir = alloc_printf("%s/rlimit", data->probe_case_dir);
    if (mkdir(data->probe_terminal_dir, 0755) && errno != EEXIST) {
      PFATAL("cannot create terminal probe directory %s",
             data->probe_terminal_dir);
    }
    if (mkdir(data->probe_rlimit_dir, 0755) && errno != EEXIST) {
      PFATAL("cannot create rlimit probe directory %s",
             data->probe_rlimit_dir);
    }
    fprintf(stderr, "[pcbt] probe cases: %s (queue/bitmap isolated)\n",
            data->probe_case_dir);
  }
  if (getenv("SYMAFL_PROBE_DIAG")) {
    data->probe_diag = true;
    fprintf(stderr, "[pcbt] probe diagnostic enabled (SYMAFL_PROBE_DIAG=1)\n");
  }
  if (getenv("SYMAFL_PROBE_LEARN")) {
    data->probe_learn = true;
    fprintf(stderr, "[pcbt] probe learn enabled (SYMAFL_PROBE_LEARN=1): "
                    "a coverage-gaining rlimit probe inserts its suffix and "
                    "refreshes the frontier edge's retry budget\n");
  }
  if (const char *pl = getenv("SYMAFL_PAIR_LOG")) {
    data->pair_log_path = (char *)ck_strdup((u8 *)pl);
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
  if (const char *agl = getenv("SYMAFL_ADMITTED_GAINED_LOG")) {
    data->admitted_gained_log = fopen(agl, "w");
    if (!data->admitted_gained_log) {
      FATAL("cannot open SYMAFL_ADMITTED_GAINED_LOG=%s", agl);
    }
    fprintf(stderr, "[pcbt] admitted-gained log: %s\n", agl);
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

extern "C" u32 afl_custom_fuzz_count(my_mutator_t *data, const u8 *buf,
                                     size_t buf_size) {
  (void)buf;
  (void)buf_size;
  if (data->current_closures.empty()) return 0;
  uint32_t n = (uint32_t)data->current_closures.size() * 32u;
  if (n < 16) n = 16;
  if (n > 256) n = 256;
  return n;
}

static uint32_t focused_rand(my_mutator_t *data, uint32_t limit) {
  if (limit <= 1) return 0;
  data->focused_rng = data->focused_rng * 6364136223846793005ULL + 1;
  return (uint32_t)(data->focused_rng >> 33) % limit;
}

static bool eval_focused(my_mutator_t *data, const pcbt::AttachedClosure &c,
                         const u8 *buf, uint32_t len) {
  if (data->worker_mode && data->worker.tree) {
    uint32_t np =
        data->worker.tree->hdr.n_preds.load(std::memory_order_acquire);
    return pcbt::eval_e_use(data->worker.tree->preds, np, c, buf, len);
  }
  return data->tree.eval_attached(c, buf, len);
}

extern "C" size_t afl_custom_fuzz(my_mutator_t *data, u8 *buf, size_t buf_size,
                                  u8 **out_buf, u8 *add_buf,
                                  size_t add_buf_size, size_t max_size) {
  (void)add_buf;
  (void)add_buf_size;
  (void)max_size;
  data->focused_tried += 1;
  if (data->current_closures.empty() || buf_size == 0) {
    *out_buf = buf;
    return 0;
  }
  const pcbt::AttachedClosure &c =
      data->current_closures[data->focused_rr++ % data->current_closures.size()];
  if (c.s.empty()) {
    *out_buf = buf;
    return 0;
  }
  if (data->focused_scratch.size() < buf_size)
    data->focused_scratch.resize(buf_size);
  memcpy(data->focused_scratch.data(), buf, buf_size);
  uint32_t off = c.s[focused_rand(data, (u32)c.s.size())];
  if (off >= buf_size) {
    data->focused_screened += 1;
    *out_buf = data->focused_scratch.data();
    return 0;
  }
  data->focused_scratch[off] = (u8)focused_rand(data, 256);
  if (!eval_focused(data, c, data->focused_scratch.data(),
                    (uint32_t)buf_size)) {
    data->focused_screened += 1;
    *out_buf = data->focused_scratch.data();
    return 0;
  }
  data->focused_exec += 1;
  *out_buf = data->focused_scratch.data();
  return buf_size;
}

extern "C" void afl_custom_deinit(my_mutator_t *data) {
  write_progress(data, true);
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt] traces=%llu nodes=%llu pred_nodes=%llu depth=%llu conflicts=%llu "
          "opaque=%llu tautology=%llu struct_err=%llu struct_convert=%llu struct_train=%llu failed=%llu timeouts=%llu memerr=%llu screened=%llu "
          "admitted=%llu vetoed=%llu traced_entries=%llu saturated=%llu "
          "single_pass=%llu single_pass_overflow=%llu "
          "admit_empty=%llu admit_opaque=%llu follow_tautology=%llu admit_eval_failure=%llu admit_frontier=%llu admit_unstable=%llu "
          "admit_len_veto=%llu veto_terminal=%llu veto_rlimit=%llu veto_unstable=%llu probe_admitted=%llu probe_gained=%llu "
          "probe_gained_terminal=%llu probe_gained_rlimit=%llu profile=%d "
          "concolic_runs=%llu concolic_failed=%llu "
          "san_runs=%llu san_tmouts=%llu san_crashes=%llu san_saved=%llu "
          "check_ns=%llu check_calls=%llu trace_ns=%llu trace_calls=%llu "
          "replay_ns=%llu replay_calls=%llu decode_ns=%llu decode_calls=%llu "
          "insert_ns=%llu insert_calls=%llu exec_ns=%llu exec_calls=%llu\n",
          (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
          (unsigned long long)t.num_pred_nodes(),
          (unsigned long long)t.max_depth,
          (unsigned long long)t.num_conflicts,
          (unsigned long long)t.num_opaque,
          (unsigned long long)t.num_tautology,
          (unsigned long long)t.insert_structural_error,
          (unsigned long long)t.insert_struct_convert_fail,
          (unsigned long long)t.insert_struct_train_mismatch,
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
          (unsigned long long)t.check_follow_tautology,
          (unsigned long long)t.check_admit_eval_failure,
          (unsigned long long)t.check_admit_frontier,
          (unsigned long long)t.check_admit_unstable,
          (unsigned long long)t.check_admit_len_veto,
          (unsigned long long)t.check_veto_terminal,
          (unsigned long long)t.check_veto_rlimit,
          (unsigned long long)t.check_veto_unstable,
          (unsigned long long)data->veto_probe_admitted,
          (unsigned long long)data->veto_probe_gained,
          (unsigned long long)data->probe_gained_terminal,
          (unsigned long long)data->probe_gained_rlimit,
          (int)(data->profile_enabled ? 1 : 0),
          (unsigned long long)data->concolic_run_calls,
          (unsigned long long)data->concolic_run_failed,
          (unsigned long long)data->san_run_calls,
          (unsigned long long)data->san_tmouts,
          (unsigned long long)data->san_crashes,
          (unsigned long long)data->san_crashes_saved,
          (unsigned long long)data->profile_check_ns,
          (unsigned long long)data->profile_check_calls,
          (unsigned long long)data->profile_trace_ns,
          (unsigned long long)data->profile_trace_calls,
          (unsigned long long)data->profile_replay_ns,
          (unsigned long long)data->profile_replay_calls,
          (unsigned long long)data->profile_decode_ns,
          (unsigned long long)data->profile_decode_calls,
          (unsigned long long)data->profile_insert_ns,
          (unsigned long long)data->profile_insert_calls,
          (unsigned long long)data->profile_exec_ns,
          (unsigned long long)data->profile_exec_calls);
  fprintf(stderr,
          "[pcbt] focused_tried=%llu focused_screened=%llu focused_exec=%llu "
          "closure_seeds=%llu\n",
          (unsigned long long)data->focused_tried,
          (unsigned long long)data->focused_screened,
          (unsigned long long)data->focused_exec,
          (unsigned long long)data->closures_by_file.size());
  if (data->forensics_dir || data->anomaly_case_dir) {
    fprintf(stderr,
            "[pcbt-forensics] dir=%s anomaly_dir=%s opaque_seen=%llu "
            "opaque_captured=%llu opaque_suppressed=%llu terminal_seen=%llu "
            "terminal_captured=%llu terminal_suppressed=%llu "
            "struct_seen=%llu struct_captured=%llu struct_suppressed=%llu "
            "entry_seen=%llu entry_captured=%llu entry_suppressed=%llu "
            "replay_seen=%llu replay_captured=%llu replay_suppressed=%llu\n",
            data->forensics_dir ? data->forensics_dir : "(none)",
            data->anomaly_case_dir ? data->anomaly_case_dir : "(none)",
            (unsigned long long)data->forensic_opaque_seen,
            (unsigned long long)data->forensic_opaque_captured,
            (unsigned long long)data->forensic_opaque_suppressed,
            (unsigned long long)data->forensic_terminal_seen,
            (unsigned long long)data->forensic_terminal_captured,
            (unsigned long long)data->forensic_terminal_suppressed,
            (unsigned long long)data->forensic_struct_seen,
            (unsigned long long)data->forensic_struct_captured,
            (unsigned long long)data->forensic_struct_suppressed,
            (unsigned long long)data->forensic_entry_seen,
            (unsigned long long)data->forensic_entry_captured,
            (unsigned long long)data->forensic_entry_suppressed,
            (unsigned long long)data->forensic_replay_seen,
            (unsigned long long)data->forensic_replay_captured,
            (unsigned long long)data->forensic_replay_suppressed);
  }
  if (t.insert_structural_error) {
    fprintf(stderr,
            "[pcbt-struct] total=%llu convert_fail=%llu train_mismatch=%llu\n",
            (unsigned long long)t.insert_structural_error,
            (unsigned long long)t.insert_struct_convert_fail,
            (unsigned long long)t.insert_struct_train_mismatch);
    if (!t.struct_error_by_cid.empty()) {
      std::vector<std::pair<uint32_t, uint64_t>> ranked(
          t.struct_error_by_cid.begin(), t.struct_error_by_cid.end());
      std::sort(ranked.begin(), ranked.end(),
                [](const auto &a, const auto &b) { return a.second > b.second; });
      const size_t n = ranked.size() < 32 ? ranked.size() : 32;
      for (size_t i = 0; i < n; ++i) {
        fprintf(stderr, "[pcbt-struct-cid] cid=%u count=%llu\n",
                ranked[i].first, (unsigned long long)ranked[i].second);
      }
    }
  }
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
          "terminal_match=%llu timeout_skipped=%llu "
          "crash_skipped=%llu entry_artifact=%llu "
          "short_capture_skipped=%llu\n",
          (unsigned long long)data->replay_checked,
          (unsigned long long)data->replay_cid_mismatch,
          (unsigned long long)data->replay_direction_mismatch,
          (unsigned long long)data->replay_after_terminal,
          (unsigned long long)data->replay_truncated,
          (unsigned long long)data->replay_frontier_match,
          (unsigned long long)data->replay_terminal_match,
          (unsigned long long)data->replay_timeout_skipped,
          (unsigned long long)data->replay_crash_skipped,
          (unsigned long long)data->replay_entry_artifact,
          (unsigned long long)data->replay_short_capture_skipped);
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
                                       &vnode, &vdir, &vkind,
                                       data->len_rlimit);
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
  if (data->admitted_gained_log) fclose(data->admitted_gained_log);
  delete data;
}


static void disarm_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  if (!control) {
    data->single_pass_armed = false;
    data->root_shm_capture = false;
    return;
  }
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELEASE);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_OFF, __ATOMIC_RELEASE);
  data->single_pass_armed = false;
  data->root_shm_capture = false;
}

static void arm_full_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  if (!control) return;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  // FULL_STREAM does not consult skip_depth for emission, but clear any
  // leftover suffix skip so diagnostics and pipe-suffix arming stay honest.
  control->skip_depth = 0;
  __atomic_store_n(&control->mode, SYMAFL_TRACE_FULL_STREAM, __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->single_pass_armed = true;
  data->root_shm_capture = false;
}

static void arm_root_shm_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  if (!control) return;
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
  if (!control) return;
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
      uint8_t rsan_bug = (msg.flags & F_RSAN_CHECK)
          ? (uint8_t)((msg.flags & F_RSAN_BUG_DIR) ? 1 : 0)
          : 0xff;
      events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0),
                         is_constraint, 1, rsan_bug});
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
  // Intentionally silent: per-call decode logging on REPLAY_ALL filled a 22 G
  // afl-fuzz.log and the root disk. Drop counts are unused outside diagnostics.
  (void)n_cond;
  (void)n_dropped_zero;
  (void)n_dropped_init;
  return true;
}

// The forkserver that executes the concolic target. Its children write the
// condition frames into the mutator-owned pipe; the drain machinery
// (read_s32_timed_with_trace / drain_sym_trace_complete) fills its
// sym_trace_buf/len, and its child_status / last_run_timed_out /
// last_kill_signal describe the concolic run.
static inline afl_forkserver_t *concolic_fsrv(my_mutator_t *data) {
  return &data->afl->fsrv_concolic;
}

static bool decode_pipe_events(my_mutator_t *data,
                               std::vector<pcbt::Event> *events,
                               const char *fname) {
  afl_forkserver_t *fsrv = concolic_fsrv(data);
  if (decode_full_stream(fsrv->sym_trace_buf, fsrv->sym_trace_len, events)) {
    return true;
  }
  WARNF("invalid pipe trace for %s (%zu bytes)\n", fname,
        fsrv->sym_trace_len);
  data->failed_runs += 1;
  return false;
}

// Quality contract: first hard residual aborts the instance (keep forensics).
// Does not fire for transport demotions (short_capture_skipped) or stop_soon
// empty captures. Marker files let lean-pcbt-run / hunt-residuals stop the
// outer campaign without waiting for MIN_SCREENED.
static void request_residual_abort(my_mutator_t *data, const char *reason) {
  if (!data || !data->abort_on_residual || data->residual_abort_fired) return;
  data->residual_abort_fired = true;
  data->afl->stop_soon = 1;
  fprintf(stderr,
          "[pcbt-abort] residual=%s — stop_soon=1; keep forensics; "
          "do not continue testing until RCA/fix\n",
          reason ? reason : "unknown");
  // Prefer forensics parent (EVID/) then forensics_dir itself.
  auto write_marker = [](const char *path, const char *reason) {
    if (!path || !*path) return;
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "residual=%s\n", reason ? reason : "unknown");
    fprintf(f, "action=retain_logs_and_exit\n");
    fprintf(f, "next=RCA_then_fix_then_retest\n");
    fclose(f);
  };
  if (data->forensics_dir) {
    char marker[PATH_MAX];
    // $EVID/forensics -> $EVID/ABORT_RESIDUAL
    snprintf(marker, sizeof(marker), "%s/../ABORT_RESIDUAL",
             data->forensics_dir);
    write_marker(marker, reason);
    snprintf(marker, sizeof(marker), "%s/ABORT_RESIDUAL", data->forensics_dir);
    write_marker(marker, reason);
  }
}

// Direct re-exec of the concolic target for TruncatedTrace isolation.
// Uses posix_spawn (AFL is multi-threaded; plain fork is unsafe).
// Returns true when a stream was collected into *out.
// Direct re-exec. When out_wire is non-null, also returns the raw pipe bytes
// (for admit-pipe.bin pair forensics).
static bool reexec_full_stream(my_mutator_t *data, const u8 *buf,
                               size_t buf_size, std::vector<pcbt::Event> *out,
                               std::vector<u8> *out_wire = nullptr) {
  if (!data->concolic_target || !buf || buf_size == 0 || !out) return false;
  out->clear();
  if (out_wire) out_wire->clear();

  char tmpl[] = "/home/hahafish/symafl2-work/pcbt-reexec-XXXXXX";
  int ifd = mkstemp(tmpl);
  if (ifd < 0) {
    fprintf(stderr, "[pcbt-reexec] mkstemp failed: %s\n", strerror(errno));
    return false;
  }
  if (write(ifd, buf, buf_size) != (ssize_t)buf_size) {
    close(ifd);
    unlink(tmpl);
    return false;
  }
  close(ifd);

  int pipefd[2];
  if (pipe(pipefd) != 0) {
    unlink(tmpl);
    return false;
  }

  char taint[512];
  snprintf(taint, sizeof(taint),
           "taint_file=%s:taint_max_len=65536:pipe_fd=%d:exit_on_memerror=false",
           tmpl, pipefd[1]);

  // Build env with TAINT_OPTIONS override.
  std::vector<char *> envp;
  for (char **e = environ; e && *e; ++e) {
    if (strncmp(*e, "TAINT_OPTIONS=", 14) == 0) continue;
    if (strncmp(*e, "SYMAFL_TRACE_MODE=", 18) == 0) continue;
    envp.push_back(*e);
  }
  char taint_env[560];
  snprintf(taint_env, sizeof(taint_env), "TAINT_OPTIONS=%s", taint);
  envp.push_back(taint_env);
  envp.push_back(nullptr);

  char *argv[] = {data->concolic_target, tmpl, nullptr};
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  // Child keeps write end; close read end in child.
  posix_spawn_file_actions_addclose(&fa, pipefd[0]);

  pid_t pid = 0;
  int sp = posix_spawn(&pid, data->concolic_target, &fa, nullptr, argv,
                       envp.data());
  posix_spawn_file_actions_destroy(&fa);
  close(pipefd[1]);  // parent keeps read end only — enables EOF after child exit
  if (sp != 0) {
    fprintf(stderr, "[pcbt-reexec] posix_spawn failed: %s\n", strerror(sp));
    close(pipefd[0]);
    unlink(tmpl);
    return false;
  }

#ifdef F_SETPIPE_SZ
  (void)fcntl(pipefd[0], F_SETPIPE_SZ, 1 << 20);
#endif

  // Non-blocking poll until the child exits, then a blocking drain to EOF.
  // The old 8s/800×10ms loop SIGKILL'd long DFSan runs and returned a pure
  // prefix of the true stream (e.g. 550 of 2371), which failed demotion and
  // left transport short captures counted as hard truncated.
  int flags = fcntl(pipefd[0], F_GETFL);
  if (flags >= 0) fcntl(pipefd[0], F_SETFL, flags | O_NONBLOCK);

  std::vector<u8> wire;
  wire.reserve(1 << 16);
  u8 chunk[8192];
  const int max_rounds = 6000;  // ~60s at 10ms
  bool child_done = false;
  int st = 0;
  for (int r = 0; r < max_rounds; ++r) {
    for (;;) {
      ssize_t n = read(pipefd[0], chunk, sizeof(chunk));
      if (n > 0) {
        wire.insert(wire.end(), chunk, chunk + n);
        continue;
      }
      if (n == 0) { child_done = true; break; }  // EOF
      if (errno == EAGAIN || errno == EWOULDBLOCK) break;
      child_done = true;
      break;
    }
    if (child_done) break;
    pid_t w = waitpid(pid, &st, WNOHANG);
    if (w == pid) {
      // Blocking drain to EOF now that the writer has exited.
      if (flags >= 0) fcntl(pipefd[0], F_SETFL, flags & ~O_NONBLOCK);
      for (;;) {
        ssize_t n = read(pipefd[0], chunk, sizeof(chunk));
        if (n > 0) wire.insert(wire.end(), chunk, chunk + n);
        else break;
      }
      child_done = true;
      break;
    }
    struct timeval tv = {0, 10000};
    select(0, nullptr, nullptr, nullptr, &tv);
  }
  if (!child_done) {
    kill(pid, SIGKILL);
    waitpid(pid, &st, 0);
    if (flags >= 0) fcntl(pipefd[0], F_SETFL, flags & ~O_NONBLOCK);
    for (;;) {
      ssize_t n = read(pipefd[0], chunk, sizeof(chunk));
      if (n > 0) wire.insert(wire.end(), chunk, chunk + n);
      else break;
    }
    fprintf(stderr, "[pcbt-reexec] killed after timeout wire=%zu\n",
            wire.size());
  }
  close(pipefd[0]);
  unlink(tmpl);

  if (wire.empty()) {
    fprintf(stderr, "[pcbt-reexec] empty wire (child rc/signal?)\n");
    return false;
  }
  std::vector<pcbt::Event> decoded;
  if (!decode_full_stream(wire.data(), wire.size(), &decoded)) {
    fprintf(stderr, "[pcbt-reexec] decode failed wire=%zu\n", wire.size());
    return false;
  }
  fprintf(stderr, "[pcbt-reexec] wire=%zu events=%zu\n", wire.size(),
          decoded.size());
  if (out_wire) *out_wire = wire;
  *out = std::move(decoded);
  return true;
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

static bool capture_anomaly_case(
    my_mutator_t *data, const char *reason,
    const std::vector<pcbt::Event> &events, const u8 *input, size_t input_len,
    pcbt::NodeRef mismatch_node = pcbt::kUnexplored, size_t event_index = 0,
    uint32_t expected_cid = 0, uint32_t observed_cid = 0);

static bool replay_check_trace(my_mutator_t *data,
                               const std::vector<pcbt::Event> &events,
                               const u8 *buf, size_t buf_size,
                               const char *fname, bool is_suffix) {
  if (!data->replay_check) return true;
  // A timed-out target execution was SIGKILLed by AFL (last_run_timed_out +
  // last_kill_signal==SIGKILL); its trace is incomplete by construction, not
  // because the tree disagrees with it. Replaying it would fabricate
  // truncated/conflict signals and mark nodes unstable for an execution that
  // was interrupted, not divergent. Count it separately and skip: timeout
  // handling is a performance/robustness concern, not a decision-omission
  // signal.
  if (concolic_fsrv(data)->last_run_timed_out) {
    data->replay_timeout_skipped += 1;
    return true;
  }
  // Crash / signal death on THIS run (e.g. SIGSEGV). Use WIFSIGNALED on the
  // current child_status — fsrv.last_kill_signal is sticky (not cleared on
  // FSRV_RUN_OK) and would false-positive every later run after one crash.
  // Incomplete stream by construction, not entry_artifact / truncated.
  // Timeouts already returned above (also WIFSIGNALED with SIGKILL).
  if (WIFSIGNALED(concolic_fsrv(data)->child_status)) {
    data->replay_crash_skipped += 1;
    WARNF("[pcbt-replay] crash-skipped: kill_sig=%u events=%zu "
          "pipe_bytes=%zu input_len=%zu; skip\n",
          (unsigned)WTERMSIG(concolic_fsrv(data)->child_status), events.size(),
          concolic_fsrv(data)->sym_trace_len, buf_size);
    (void)capture_anomaly_case(data, "crash-skipped", events, buf, buf_size);
    return true;
  }
  // post_run already replayed this run's full stream (SYMAFL_REPLAY_ALL);
  // queue_new_entry's insert must not count it a second time.
  if (data->replay_run_done) {
    data->replay_run_done = false;
    return true;
  }
  // Entry-fork / empty-capture artifact guard (restored from aeda20e,
  // broadened). Transport defects, not tree decision omissions:
  //   (1) empty full stream with non-empty input (taint not registered, mode
  //       OFF, or pipe write never happened) — always quarantine;
  //   (2) non-empty full stream whose first event is not a constraint while
  //       the learned tree entry is a constraint (stale/partial pipe).
  // Always dump the candidate input + raw pipe into anomaly-cases so the
  // counter is reproducible offline.
  // Note: crash/timeout already returned above, so empty streams here are
  // clean-exit empty captures (true transport/path defects) — unless AFL is
  // shutting down (SIGINT after MIN_SCREENED). Abort/teardown often leaves one
  // empty full capture that is not a taint-path defect.
  if (!is_suffix) {
    const pcbt::NodeRef entry = data->tree.root_child0();
    const bool have_entry =
        entry != pcbt::kUnexplored && entry != pcbt::kTerminal;
    const bool entry_is_constraint =
        have_entry && data->tree.is_constraint(entry);
    const bool empty_nonempty_input = events.empty() && buf_size > 0;
    const bool first_not_constraint =
        entry_is_constraint && !events.empty() && !events.front().constraint;
    if (empty_nonempty_input || first_not_constraint) {
      // stop_soon is set when the user/watcher SIGINTs afl-fuzz for a clean
      // deinit. Quarantine without inflating entry_artifact (supporting RQ1
      // diagnostic must not be poisoned by shutdown races).
      if (data->afl->stop_soon && empty_nonempty_input) {
        WARNF("[pcbt-replay] entry-empty during stop_soon: pipe_bytes=%zu "
              "input_len=%zu; skip (not entry_artifact)\n",
              concolic_fsrv(data)->sym_trace_len, buf_size);
        return true;
      }
      data->replay_entry_artifact += 1;
      WARNF("[pcbt-replay] entry-fork artifact: first event cid=%u "
            "constraint=%u events=%zu vs entry cid=%u entry_constraint=%d; "
            "pipe_bytes=%zu kill_sig=%u timeout=%u; skip\n",
            events.empty() ? 0 : events.front().cid,
            events.empty() ? 0u : (events.front().constraint ? 1u : 0u),
            events.size(),
            have_entry ? data->tree.cid_of(entry) : 0u,
            entry_is_constraint ? 1 : 0, concolic_fsrv(data)->sym_trace_len,
            concolic_fsrv(data)->last_kill_signal,
            concolic_fsrv(data)->last_run_timed_out);
      (void)capture_anomaly_case(data, "entry-artifact", events, buf,
                                 buf_size);
      request_residual_abort(data, "entry_artifact");
      return true;
    }
  }
  // A full capture must validate an empty stream against the learned tree:
  // an empty child trace can be truncated before the next learned event. A
  // suffix intentionally omits the known prefix and cannot use this replay
  // walk without reconstructing that prefix.
  if (events.empty() && is_suffix) return true;

  data->replay_checked += 1;
  auto report = data->tree.ReplayFullTrace(events, buf,
                                           (uint32_t)buf_size);

  if (report.error == pcbt::Tree::ReplayError::None) {
    if (report.reached_terminal) data->replay_terminal_match += 1;
    else if (report.reached_frontier) data->replay_frontier_match += 1;
    return true;
  }

  // TruncatedTrace + clean exit: the in-AFL pipe may be an incomplete
  // capture of a longer stream (observed: same input direct=3122 events,
  // AFL pipe=1033 pure prefix). Re-exec once without the forkserver SHM
  // control block; if the full stream continues or diverges, demote to
  // short_capture_skipped (transport), not hard truncated.
  if (report.error == pcbt::Tree::ReplayError::TruncatedTrace && buf &&
      buf_size > 0 && !is_suffix &&
      !WIFSIGNALED(concolic_fsrv(data)->child_status) &&
      !concolic_fsrv(data)->last_run_timed_out && data->concolic_target) {
    std::vector<pcbt::Event> re_events;
    if (reexec_full_stream(data, buf, buf_size, &re_events)) {
      if (re_events.size() > events.size()) {
        auto re_report =
            data->tree.ReplayFullTrace(re_events, buf, (uint32_t)buf_size);
        const bool demote =
            re_report.error == pcbt::Tree::ReplayError::None ||
            re_report.error == pcbt::Tree::ReplayError::CidMismatch ||
            re_report.error == pcbt::Tree::ReplayError::DirectionMismatch ||
            re_report.error == pcbt::Tree::ReplayError::AfterTerminal;
        if (demote) {
          data->replay_short_capture_skipped += 1;
          fprintf(stderr,
                  "[pcbt-replay] short-capture-skipped: in_afl_events=%zu "
                  "reexec_events=%zu re_error=%d (not hard truncated)\n",
                  events.size(), re_events.size(), (int)re_report.error);
          (void)capture_anomaly_case(data, "short-capture", events, buf,
                                     buf_size);
          return true;
        }
        fprintf(stderr,
                "[pcbt-replay] reexec still truncated: in_afl=%zu reexec=%zu "
                "verified=%zu (true pure-prefix hole)\n",
                events.size(), re_events.size(), re_report.verified_events);
      } else {
        fprintf(stderr,
                "[pcbt-replay] reexec not longer: in_afl=%zu reexec=%zu\n",
                events.size(), re_events.size());
      }
    }
  }

  // Replay-validation mismatches are trace conflicts too: count them in the
  // tree's conflict census so the `conflicts` metric does not hide replay
  // drift that marks nodes unstable (admit_unstable) behind a zero. A
  // TruncatedTrace is NOT benign: the candidate's stream ends in the middle
  // of a tree path, so the candidate did not pass the tree's decision at
  // that node - an entry/decision omission. Never widen the census to mask
  // it.
  data->tree.num_conflicts += 1;

  // Log the mismatch. The trace is discarded so it never grows the tree with
  // an unverified path; the divergence is a collection/derivation defect to
  // diagnose, not something the tree should learn around.
  const char *err_name = "unknown";
  const char *case_reason = "replay-mismatch";
  switch (report.error) {
    case pcbt::Tree::ReplayError::CidMismatch:
      err_name = "cid_mismatch";
      case_reason = "cid-mismatch";
      data->replay_cid_mismatch += 1;
      break;
    case pcbt::Tree::ReplayError::DirectionMismatch:
      err_name = "direction_mismatch";
      case_reason = "dir-mismatch";
      data->replay_direction_mismatch += 1;
      break;
    case pcbt::Tree::ReplayError::AfterTerminal:
      err_name = "after_terminal";
      case_reason = "after-terminal";
      data->replay_after_terminal += 1;
      break;
    case pcbt::Tree::ReplayError::TruncatedTrace:
      err_name = "truncated";
      case_reason = "truncated";
      data->replay_truncated += 1;
      break;
    default: break;
  }
  // Hard residual (not short_capture demotion): abort quality instance now.
  request_residual_abort(data, err_name);
  if (report.mismatch_node != pcbt::kUnexplored) {
    // A truncated trace (stream ends mid-path) is a structural disagreement
    // like any other: the tree claims a decision here that the candidate's
    // stream does not contain. Marking the node unstable is the exposure
    // mechanism - the divergence must be diagnosed and the tree made
    // correct, never hidden by widening the acceptance criteria.
    data->tree.mark_unstable(report.mismatch_node);
  }
  WARNF("[pcbt-replay] %s mismatch %s at event=%zu verified=%zu "
        "expected_cid=%u observed_cid=%u eval_dir=%u obs_dir=%u %s\n",
        fname, err_name, report.event_index, report.verified_events,
        report.expected_cid, report.observed_cid,
        report.evaluated_dir, report.observed_dir,
        is_suffix ? "suffix" : "full");
  if (data->tree.conflict_diag() && buf && buf_size > 0 &&
      report.error != pcbt::Tree::ReplayError::TruncatedTrace) {
    static uint64_t diag_mismatch_inputs = 0;
    if (diag_mismatch_inputs < 8) {
      diag_mismatch_inputs++;
      size_t shown = buf_size < 64 ? buf_size : 64;
      fprintf(stderr, "[pcbt-replay] %s mismatch input len=%zu hex=",
              err_name, buf_size);
      for (size_t k = 0; k < shown; ++k)
        fprintf(stderr, "%02x", buf[k]);
      fprintf(stderr, "%s\n", shown < buf_size ? " TRUNC" : "");
    }
  }
  if (data->tree.conflict_diag() &&
      report.mismatch_node != pcbt::kUnexplored &&
      report.error != pcbt::Tree::ReplayError::TruncatedTrace && buf) {
    // Dump the stored predicate at the mismatch node so the branch site can
    // be identified (which bytes it reads, what comparison it performs).
    data->tree.DebugPredicate(report.mismatch_node, buf, (uint32_t)buf_size);
  }
  if (report.error == pcbt::Tree::ReplayError::TruncatedTrace && buf &&
      buf_size > 0) {
    // Always-on truncated forensics: complete stream ended mid-tree-path.
    // The short execution should have diverged earlier or closed a Terminal;
    // dump last events + the next expected node for RCA.
    // last_kill_signal is sticky across OK runs — only report a kill when
    // THIS run's child_status is signalled (or a true timeout already
    // returned above). Sticky SIGKILL from an earlier hang was poisoning
    // truncated meta and hiding real clean-exit pure-prefix holes.
    const uint32_t run_kill =
        WIFSIGNALED(concolic_fsrv(data)->child_status)
            ? (uint32_t)WTERMSIG(concolic_fsrv(data)->child_status)
            : 0u;
    size_t shown = buf_size < 64 ? buf_size : 64;
    fprintf(stderr,
            "[pcbt-replay] truncated input len=%zu events=%zu "
            "verified=%zu pipe_bytes=%zu kill_sig=%u timeout=%u hex=",
            buf_size, events.size(), report.verified_events,
            concolic_fsrv(data)->sym_trace_len, run_kill,
            concolic_fsrv(data)->last_run_timed_out);
    for (size_t k = 0; k < shown; ++k)
      fprintf(stderr, "%02x", buf[k]);
    fprintf(stderr, "%s\n", shown < buf_size ? " TRUNC" : "");
    if (!events.empty()) {
      size_t n = events.size() < 5 ? events.size() : 5;
      fprintf(stderr, "[pcbt-replay] truncated last_events:");
      for (size_t k = events.size() - n; k < events.size(); ++k) {
        const pcbt::Event &ev = events[k];
        fprintf(stderr, " [%zu cid=%u res=%u c=%u n=%u]", k, ev.cid, ev.result,
                ev.constraint, ev.count);
      }
      fprintf(stderr, "\n");
    }
    if (report.mismatch_node != pcbt::kUnexplored) {
      fprintf(stderr,
              "[pcbt-replay] truncated at tree node=%u cid=%u depth=%u "
              "constraint=%d len_related=%d (next expected after full short "
              "stream; short should have Terminal or earlier diverge)\n",
              report.mismatch_node,
              data->tree.cid_of(report.mismatch_node),
              data->tree.depth(report.mismatch_node),
              data->tree.is_constraint(report.mismatch_node) ? 1 : 0,
              data->tree.is_len_related(report.mismatch_node) ? 1 : 0);
      data->tree.DebugPredicate(report.mismatch_node, buf, (uint32_t)buf_size);
    }
  }
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
  // Dump PROBE (this candidate) + ADMIT (creator of mismatch_node) so RCA
  // always has a real test-case pair, not probe-only guesswork.
  (void)capture_anomaly_case(data, case_reason, events, buf, buf_size,
                             report.mismatch_node, report.event_index,
                             report.expected_cid, report.observed_cid);
  return false;  // discard mismatched trace
}

struct ForensicSnapshotMeta {
  const char *trace_mode = "unknown";
  uint32_t skip_depth = 0;
  uint32_t raw_event_count = 0;
  bool trace_overflow = false;
  uint64_t opaque_before = 0;
  uint64_t opaque_after = 0;
  pcbt::NodeRef veto_node = pcbt::kUnexplored;
  uint8_t veto_dir = 0;
  uint8_t veto_kind = 0;
  uint32_t veto_depth = 0;
  uint8_t new_bits = 0;
  const char *pair_log = nullptr;
  // Structural-fault forensics (insert convert_fail / train_mismatch).
  uint32_t struct_cid = 0;
  uint32_t struct_label = 0;
  uint8_t struct_result = 0;
  size_t struct_event_index = 0;
  uint8_t struct_from_suffix = 0;
};

static void write_forensic_input(const std::string &path, const u8 *input,
                                 size_t input_len) {
  int fd = open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
  if (fd < 0) PFATAL("cannot create forensic input %s", path.c_str());
  if (input_len) ck_write(fd, const_cast<u8 *>(input), input_len, path.c_str());
  close(fd);
}

// Persist a hard-anomaly test case so counters are always actionable.
// Writes under anomaly_case_dir:
//   case-NNNNNN-<reason>-input.bin          (PROBE: the mismatched candidate)
//   case-NNNNNN-<reason>-pipe.bin
//   case-NNNNNN-<reason>-events.tsv
//   case-NNNNNN-<reason>-meta.txt
//   case-NNNNNN-<reason>-admit-input.bin    (ADMIT: first creator of mismatch
//                                           tree node, when stored)
//   case-NNNNNN-<reason>-admit-events.tsv   (reexec of admit, best-effort)
//   case-NNNNNN-<reason>-admit-pipe.bin
//   index.tsv (append one row)
// Entry-artifact cases use a high limit (default max(forensic_limit, 64));
// replay mismatches share the same budget so rare faults are not dropped.
// mismatch_node / expected_cid / observed_cid are optional pair forensics
// (pass kUnexplored / 0 when unknown).
static bool capture_anomaly_case(my_mutator_t *data, const char *reason,
                                 const std::vector<pcbt::Event> &events,
                                 const u8 *input, size_t input_len,
                                 pcbt::NodeRef mismatch_node,
                                 size_t event_index, uint32_t expected_cid,
                                 uint32_t observed_cid) {
  if (!data->anomaly_case_dir) return false;

  const bool is_entry = (strcmp(reason, "entry-artifact") == 0);
  uint64_t *seen = is_entry ? &data->forensic_entry_seen
                            : &data->forensic_replay_seen;
  uint64_t *captured = is_entry ? &data->forensic_entry_captured
                                : &data->forensic_replay_captured;
  uint64_t *suppressed = is_entry ? &data->forensic_entry_suppressed
                                  : &data->forensic_replay_suppressed;
  // Entry artifacts are rare (1–2 / 40k) — keep more dumps than generic
  // opaque/struct snapshots.
  const uint64_t limit =
      is_entry ? (data->forensic_limit < 64 ? 64 : data->forensic_limit)
               : data->forensic_limit;
  *seen += 1;
  if (*captured >= limit) {
    *suppressed += 1;
    return false;
  }

  const uint64_t sequence = data->forensic_seq++;
  char *base = alloc_printf("%s/case-%06llu-%s", data->anomaly_case_dir,
                            (unsigned long long)sequence, reason);
  std::string input_path = std::string(base) + "-input.bin";
  std::string pipe_path = std::string(base) + "-pipe.bin";
  std::string events_path = std::string(base) + "-events.tsv";
  std::string meta_path = std::string(base) + "-meta.txt";

  write_forensic_input(input_path, input, input_len);

  // Raw pipe bytes for the just-finished child (may be empty for true empty
  // streams; non-empty with empty decoded events indicates decode failure).
  {
    afl_forkserver_t *fsrv = concolic_fsrv(data);
    int pfd = open(pipe_path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (pfd >= 0) {
      if (fsrv->sym_trace_buf && fsrv->sym_trace_len) {
        ck_write(pfd, fsrv->sym_trace_buf, fsrv->sym_trace_len,
                 pipe_path.c_str());
      }
      close(pfd);
    }
  }

  FILE *event_file = fopen(events_path.c_str(), "w");
  if (event_file) {
    fprintf(event_file, "index\tcid\tlabel\tresult\tconstraint\tcount\n");
    for (size_t i = 0; i < events.size(); ++i) {
      const pcbt::Event &ev = events[i];
      fprintf(event_file, "%zu\t%u\t%u\t%u\t%u\t%u\n", i, ev.cid, ev.label,
              ev.result, ev.constraint, ev.count);
    }
    fclose(event_file);
  }

  const uint32_t mode =
      data->single_pass_control
          ? __atomic_load_n(&data->single_pass_control->mode, __ATOMIC_ACQUIRE)
          : 0u;
  const char *mode_name =
      mode == SYMAFL_TRACE_FULL_STREAM   ? "full"
      : mode == SYMAFL_TRACE_SUFFIX_SHM  ? "shm-suffix"
      : mode == SYMAFL_TRACE_SUFFIX_PIPE ? "pipe-suffix"
                                         : "off";
  const pcbt::NodeRef entry = data->tree.root_child0();
  const uint32_t entry_cid =
      (entry != pcbt::kUnexplored && entry != pcbt::kTerminal)
          ? data->tree.cid_of(entry)
          : 0u;
  const int entry_constraint =
      (entry != pcbt::kUnexplored && entry != pcbt::kTerminal)
          ? (data->tree.is_constraint(entry) ? 1 : 0)
          : -1;
  const uint32_t first_cid = events.empty() ? 0 : events.front().cid;
  const uint32_t first_constraint =
      events.empty() ? 0u : (events.front().constraint ? 1u : 0u);
  const size_t pipe_bytes = concolic_fsrv(data)->sym_trace_len;
  // Prefer this-run signal; fall back to sticky last_kill only on timeout
  // (where AFL sets last_kill_signal = child_kill_signal without always
  // leaving WIFSIGNALED visible by the time the mutator runs).
  const uint32_t kill_sig =
      WIFSIGNALED(concolic_fsrv(data)->child_status)
          ? (uint32_t)WTERMSIG(concolic_fsrv(data)->child_status)
          : (concolic_fsrv(data)->last_run_timed_out
                 ? concolic_fsrv(data)->last_kill_signal
                 : 0u);
  const uint32_t timed_out = concolic_fsrv(data)->last_run_timed_out;

  // ADMIT partner: first input that created the mismatch tree node.
  std::string admit_input_path = std::string(base) + "-admit-input.bin";
  std::string admit_events_path = std::string(base) + "-admit-events.tsv";
  std::string admit_pipe_path = std::string(base) + "-admit-pipe.bin";
  int admit_found = 0;
  size_t admit_len = 0;
  size_t admit_events_n = 0;
  size_t admit_pipe_n = 0;
  uint32_t admit_node_cid = 0;
  uint32_t admit_node_depth = 0;
  if (mismatch_node != pcbt::kUnexplored &&
      mismatch_node != pcbt::kTerminal &&
      mismatch_node != pcbt::kRoot) {
    admit_node_cid = data->tree.cid_of(mismatch_node);
    admit_node_depth = data->tree.depth(mismatch_node);
    std::vector<uint8_t> admit_buf;
    if (data->tree.creator_of(mismatch_node, &admit_buf) &&
        !admit_buf.empty()) {
      admit_found = 1;
      admit_len = admit_buf.size();
      write_forensic_input(admit_input_path, admit_buf.data(), admit_buf.size());
      // Best-effort reexec to materialize admit event stream offline.
      // (AFL-session pipe is not retained; reexec is the reproducible partner
      // trace. Note: rare env skew vs AFL is documented in meta.)
      std::vector<pcbt::Event> admit_ev;
      std::vector<u8> admit_wire;
      if (reexec_full_stream(data, admit_buf.data(), admit_buf.size(),
                             &admit_ev, &admit_wire)) {
        admit_events_n = admit_ev.size();
        admit_pipe_n = admit_wire.size();
        FILE *aef = fopen(admit_events_path.c_str(), "w");
        if (aef) {
          fprintf(aef, "index\tcid\tlabel\tresult\tconstraint\tcount\n");
          for (size_t i = 0; i < admit_ev.size(); ++i) {
            const pcbt::Event &ev = admit_ev[i];
            fprintf(aef, "%zu\t%u\t%u\t%u\t%u\t%u\n", i, ev.cid, ev.label,
                    ev.result, ev.constraint, ev.count);
          }
          fclose(aef);
        }
        int apfd = open(admit_pipe_path.c_str(), O_WRONLY | O_CREAT | O_TRUNC,
                        0600);
        if (apfd >= 0) {
          if (!admit_wire.empty()) {
            ck_write(apfd, admit_wire.data(), admit_wire.size(),
                     admit_pipe_path.c_str());
          }
          close(apfd);
        }
      }
    }
  }

  FILE *meta_file = fopen(meta_path.c_str(), "w");
  if (meta_file) {
    fprintf(meta_file, "snapshot_version=2\nreason=%s\nsequence=%llu\n",
            reason, (unsigned long long)sequence);
    fprintf(meta_file,
            "role_probe=input/pipe/events (mismatched candidate)\n"
            "role_admit=admit-input/admit-pipe/admit-events "
            "(first creator of mismatch_node)\n");
    fprintf(meta_file, "input=%s\npipe=%s\nevents=%s\n", input_path.c_str(),
            pipe_path.c_str(), events_path.c_str());
    fprintf(meta_file, "admit_input=%s\nadmit_pipe=%s\nadmit_events=%s\n",
            admit_input_path.c_str(), admit_pipe_path.c_str(),
            admit_events_path.c_str());
    fprintf(meta_file,
            "input_len=%zu\npipe_bytes=%zu\nevents=%zu\n"
            "first_cid=%u\nfirst_constraint=%u\n"
            "kill_sig=%u\ntimeout=%u\nmode=%s\nmode_raw=%u\n"
            "entry_cid=%u\nentry_constraint=%d\n"
            "armed=%u\nbootstrap_done=%u\nreplay_all=%u\n",
            input_len, pipe_bytes, events.size(), first_cid, first_constraint,
            kill_sig, timed_out, mode_name, mode, entry_cid, entry_constraint,
            data->single_pass_armed ? 1u : 0u, data->bootstrap_done ? 1u : 0u,
            data->replay_all ? 1u : 0u);
    fprintf(meta_file,
            "mismatch_node=%u\nmismatch_node_cid=%u\nmismatch_node_depth=%u\n"
            "event_index=%zu\nexpected_cid=%u\nobserved_cid=%u\n"
            "admit_found=%d\nadmit_len=%zu\nadmit_events=%zu\n"
            "admit_pipe_bytes=%zu\n"
            "admit_trace_note=reexec_not_afl_session_pipe\n",
            mismatch_node, admit_node_cid, admit_node_depth, event_index,
            expected_cid, observed_cid, admit_found, admit_len, admit_events_n,
            admit_pipe_n);
    // Hex head of input for quick grep without opening the bin.
    size_t shown = input_len < 64 ? input_len : 64;
    fprintf(meta_file, "input_hex=");
    for (size_t k = 0; k < shown; ++k)
      fprintf(meta_file, "%02x", input ? input[k] : 0);
    fprintf(meta_file, "%s\n", shown < input_len ? " TRUNC" : "");
    if (admit_found) {
      std::vector<uint8_t> ab;
      if (data->tree.creator_of(mismatch_node, &ab)) {
        size_t ashown = ab.size() < 64 ? ab.size() : 64;
        fprintf(meta_file, "admit_hex=");
        for (size_t k = 0; k < ashown; ++k)
          fprintf(meta_file, "%02x", ab[k]);
        fprintf(meta_file, "%s\n", ashown < ab.size() ? " TRUNC" : "");
      }
    }
    fclose(meta_file);
  }

  if (data->anomaly_index) {
    fprintf(data->anomaly_index,
            "%llu\t%s\t%zu\t%zu\t%zu\t%u\t%u\t%u\t%u\t%s\t%u\t%d\t%s\t"
            "admit_found=%d\tadmit_len=%zu\tmismatch_node=%u\n",
            (unsigned long long)sequence, reason, input_len, pipe_bytes,
            events.size(), first_cid, first_constraint, kill_sig, timed_out,
            mode_name, entry_cid, entry_constraint, input_path.c_str(),
            admit_found, admit_len, mismatch_node);
    fflush(data->anomaly_index);
  }

  *captured += 1;
  WARNF("[pcbt-anomaly] reason=%s case=%s probe_len=%zu pipe_bytes=%zu "
        "events=%zu admit_found=%d admit_len=%zu mismatch_node=%u "
        "expected_cid=%u observed_cid=%u mode=%s\n",
        reason, base, input_len, pipe_bytes, events.size(), admit_found,
        admit_len, mismatch_node, expected_cid, observed_cid, mode_name);
  ck_free(base);
  return true;
}

// Persist the current candidate's raw event stream and the complete label DAG
// reachable from those events.  This runs while the child-owned shared union
// table is still valid; a later forensic replay is deliberately unnecessary.
static bool capture_forensic_snapshot(
    my_mutator_t *data, const char *reason,
    const std::vector<pcbt::Event> &events, const dfsan_label_info *table,
    size_t table_labels, const u8 *input, size_t input_len,
    const ForensicSnapshotMeta &meta) {
  if (!data->forensics_dir) return false;

  uint64_t *seen_count = nullptr;
  uint64_t *captured_count = nullptr;
  uint64_t *suppressed_count = nullptr;
  if (strcmp(reason, "opaque") == 0) {
    seen_count = &data->forensic_opaque_seen;
    captured_count = &data->forensic_opaque_captured;
    suppressed_count = &data->forensic_opaque_suppressed;
  } else if (strcmp(reason, "terminal-veto-but-gain") == 0) {
    seen_count = &data->forensic_terminal_seen;
    captured_count = &data->forensic_terminal_captured;
    suppressed_count = &data->forensic_terminal_suppressed;
  } else if (strcmp(reason, "struct-convert-fail") == 0 ||
             strcmp(reason, "struct-train-mismatch") == 0) {
    seen_count = &data->forensic_struct_seen;
    captured_count = &data->forensic_struct_captured;
    suppressed_count = &data->forensic_struct_suppressed;
  } else {
    FATAL("unknown forensic snapshot reason: %s", reason);
  }
  *seen_count += 1;
  if (*captured_count >= data->forensic_limit) {
    *suppressed_count += 1;
    return false;
  }

  const uint64_t sequence = data->forensic_seq++;
  char *suffix = alloc_printf("%06llu-%s", (unsigned long long)sequence,
                               reason);
  std::string base = std::string(data->forensics_dir) + "/snapshot-" + suffix;
  ck_free(suffix);
  std::string input_path = base + "-input.bin";
  std::string events_path = base + "-events.tsv";
  std::string labels_path = base + "-labels.tsv";
  std::string tree_path = base + "-tree.tsv";
  std::string meta_path = base + "-meta.txt";

  write_forensic_input(input_path, input, input_len);

  FILE *event_file = fopen(events_path.c_str(), "w");
  if (!event_file) PFATAL("cannot create forensic events %s",
                          events_path.c_str());
  fprintf(event_file, "index\tcid\tlabel\tresult\tconstraint\tcount\n");
  for (size_t i = 0; i < events.size(); ++i) {
    const pcbt::Event &event = events[i];
    fprintf(event_file, "%zu\t%u\t%u\t%u\t%u\t%u\n", i, event.cid,
            event.label, event.result, event.constraint, event.count);
  }
  fclose(event_file);

  FILE *label_file = fopen(labels_path.c_str(), "w");
  if (!label_file) PFATAL("cannot create forensic labels %s",
                          labels_path.c_str());
  fprintf(label_file,
          "label\top\tsize\tl1\tl2\top1\top2\top1_hi\top2_hi\thash\n");
  std::unordered_set<dfsan_label> seen;
  std::vector<dfsan_label> pending;
  pending.reserve(events.size());
  for (const pcbt::Event &event : events) pending.push_back(event.label);
  while (!pending.empty()) {
    dfsan_label label = pending.back();
    pending.pop_back();
    if (label == 0 || label == kInitializingLabel || label >= table_labels) {
      continue;
    }
    if (!seen.insert(label).second) continue;
    const dfsan_label_info &info = table[label];
    fprintf(label_file, "%u\t%u\t%u\t%u\t%u\t%llu\t%llu\t%llu\t%llu\t%u\n",
            label, info.op, info.size, info.l1, info.l2,
            (unsigned long long)info.op1.i, (unsigned long long)info.op2.i,
            (unsigned long long)info.op1_hi, (unsigned long long)info.op2_hi,
            info.hash);
    if (info.l2) pending.push_back(info.l2);
    if (info.l1) pending.push_back(info.l1);
  }
  fclose(label_file);

  data->tree.Dump(tree_path.c_str());

  FILE *meta_file = fopen(meta_path.c_str(), "w");
  if (!meta_file) PFATAL("cannot create forensic metadata %s",
                         meta_path.c_str());
  const pcbt::Tree &tree = data->tree;
  fprintf(meta_file, "snapshot_version=1\nreason=%s\nsequence=%llu\n",
          reason, (unsigned long long)sequence);
  fprintf(meta_file, "input=%s\nevents=%s\nlabels=%s\ntree=%s\n",
          input_path.c_str(), events_path.c_str(), labels_path.c_str(),
          tree_path.c_str());
  fprintf(meta_file,
          "trace_mode=%s\nskip_depth=%u\nraw_event_count=%u\n"
          "captured_event_count=%zu\ntrace_overflow=%u\ninput_len=%zu\n",
          meta.trace_mode, meta.skip_depth, meta.raw_event_count, events.size(),
          meta.trace_overflow ? 1u : 0u, input_len);
  fprintf(meta_file,
          "opaque_before=%llu\nopaque_after=%llu\nopaque_delta=%llu\n"
          "tree_nodes=%llu\ntree_depth=%llu\n",
          (unsigned long long)meta.opaque_before,
          (unsigned long long)meta.opaque_after,
          (unsigned long long)(meta.opaque_after >= meta.opaque_before
                                   ? meta.opaque_after - meta.opaque_before
                                   : 0),
          (unsigned long long)tree.num_nodes,
          (unsigned long long)tree.max_depth);
  fprintf(meta_file,
          "veto_node=%u\nveto_cid=%u\nveto_dir=%u\nveto_kind=%u\n"
          "veto_depth=%u\nnew_bits=%u\n",
          meta.veto_node, meta.veto_node != pcbt::kUnexplored
                              ? tree.cid_of(meta.veto_node)
                              : 0u,
          meta.veto_dir, meta.veto_kind, meta.veto_depth, meta.new_bits);
  fprintf(meta_file, "pair_log=%s\n", meta.pair_log ? meta.pair_log : "");
  if (meta.struct_cid || meta.struct_label ||
      strcmp(reason, "struct-convert-fail") == 0 ||
      strcmp(reason, "struct-train-mismatch") == 0) {
    fprintf(meta_file,
            "struct_cid=%u\nstruct_label=%u\nstruct_result=%u\n"
            "struct_event_index=%zu\nstruct_from_suffix=%u\n",
            meta.struct_cid, meta.struct_label, meta.struct_result,
            meta.struct_event_index, meta.struct_from_suffix);
  }
  fclose(meta_file);
  *captured_count += 1;
  fprintf(stderr, "[pcbt-forensics] reason=%s snapshot=%s events=%zu labels=%zu\n",
          reason, meta_path.c_str(), events.size(), seen.size());
  return true;
}

// After InsertTrace/InsertSuffix: if a structural fault was recorded, persist
// a limited forensic snapshot (input + events + labels + tree) for root-cause
// analysis. Always on when forensics_dir is set (quality/REPLAY_ALL paths).
static void capture_structural_fault_if_any(
    my_mutator_t *data, const std::vector<pcbt::Event> &events,
    const dfsan_label_info *table, size_t table_labels, const u8 *input,
    size_t input_len, const char *trace_mode, uint32_t skip_depth,
    uint32_t raw_event_count, bool trace_overflow) {
  pcbt::Tree::StructuralFault fault;
  if (!data->tree.take_structural_fault(&fault)) return;
  const char *reason =
      fault.reason == pcbt::Tree::StructFaultReason::ConvertFail
          ? "struct-convert-fail"
          : "struct-train-mismatch";
  ForensicSnapshotMeta meta;
  meta.trace_mode = trace_mode;
  meta.skip_depth = skip_depth;
  meta.raw_event_count = raw_event_count;
  meta.trace_overflow = trace_overflow;
  meta.struct_cid = fault.cid;
  meta.struct_label = fault.label;
  meta.struct_result = fault.result;
  meta.struct_event_index = fault.event_index;
  meta.struct_from_suffix = fault.from_suffix ? 1u : 0u;
  meta.pair_log = data->pair_log_path;
  if (capture_forensic_snapshot(data, reason, events, table, table_labels,
                                input, input_len, meta)) {
    WARNF("[pcbt-struct] %s cid=%u label=%u result=%u event_index=%zu "
          "suffix=%u forensic captured\n",
          reason, fault.cid, fault.label, fault.result, fault.event_index,
          fault.from_suffix ? 1u : 0u);
  } else if (data->forensics_dir) {
    WARNF("[pcbt-struct] %s cid=%u label=%u result=%u event_index=%zu "
          "suffix=%u (forensic suppressed or unavailable)\n",
          reason, fault.cid, fault.label, fault.result, fault.event_index,
          fault.from_suffix ? 1u : 0u);
  } else {
    WARNF("[pcbt-struct] %s cid=%u label=%u result=%u event_index=%zu "
          "suffix=%u\n",
          reason, fault.cid, fault.label, fault.result, fault.event_index,
          fault.from_suffix ? 1u : 0u);
  }
}

static bool decode_probe_capture(my_mutator_t *data,
                                 std::vector<pcbt::Event> *events,
                                 uint32_t *raw_count, bool *overflow) {
  if (!data->single_pass_armed) {
    *raw_count = 0;
    *overflow = false;
    return false;
  }
  symafl_single_pass_control *control = data->single_pass_control;
  const uint32_t count = __atomic_load_n(&control->event_count,
                                         __ATOMIC_ACQUIRE);
  *raw_count = count;
  *overflow = __atomic_load_n(&control->overflow, __ATOMIC_ACQUIRE) ||
              count > control->event_capacity;
  const uint32_t available = std::min(count, control->event_capacity);
  events->reserve(available);
  for (uint32_t i = 0; i < available; ++i) {
    const symafl_single_pass_event &event = control->events[i];
    events->push_back({event.cid, event.label, event.result,
                       event.constraint,
                       static_cast<uint16_t>(event.count ? event.count : 1),
                       event.rsan_bug_dir});
  }
  return true;
}

static void capture_opaque_if_new(
    my_mutator_t *data, uint64_t opaque_before,
    const std::vector<pcbt::Event> &events, const dfsan_label_info *table,
    size_t table_labels, const u8 *input, size_t input_len,
    const char *trace_mode, uint32_t skip_depth, uint32_t raw_event_count,
    bool trace_overflow) {
  const uint64_t opaque_after = data->tree.num_opaque;
  if (opaque_after == opaque_before) return;
  ForensicSnapshotMeta meta;
  meta.trace_mode = trace_mode;
  meta.skip_depth = skip_depth;
  meta.raw_event_count = raw_event_count;
  meta.trace_overflow = trace_overflow;
  meta.opaque_before = opaque_before;
  meta.opaque_after = opaque_after;
  capture_forensic_snapshot(data, "opaque", events, table, table_labels, input,
                            input_len, meta);
  WARNF("opaque predicate encountered; forensic evidence captured\n");
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
  const uint64_t opaque_before = data->tree.num_opaque;
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
  capture_structural_fault_if_any(data, events, __dfsan_label_info, MAX_LABEL,
                                  buf, buf_size, "pipe-full", 0,
                                  (uint32_t)events.size(), false);
  capture_opaque_if_new(data, opaque_before, events, __dfsan_label_info,
                        MAX_LABEL, buf, buf_size, "pipe-full", 0,
                        (uint32_t)events.size(), false);
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
  const uint64_t opaque_before = data->tree.num_opaque;
  uint32_t created = data->tree.InsertSuffix(
      data->last_node, data->last_dir, events, __dfsan_label_info, MAX_LABEL,
      buf, (uint32_t)buf_size, out_tail_node, out_tail_dir);
  uint64_t expanded = 0;
  for (const pcbt::Event &ev : events) expanded += ev.count;
  fprintf(stderr,
          "[pcbt-trace] %s mode=pipe-suffix skip=%u events=%zu expanded=%llu "
          "created=%u\n",
          fname, data->tree.depth(data->last_node), events.size(),
          (unsigned long long)expanded, created);
  capture_structural_fault_if_any(
      data, events, __dfsan_label_info, MAX_LABEL, buf, buf_size, "pipe-suffix",
      data->tree.depth(data->last_node), (uint32_t)events.size(), false);
  capture_opaque_if_new(data, opaque_before, events, __dfsan_label_info,
                        MAX_LABEL, buf, buf_size, "pipe-suffix",
                        data->tree.depth(data->last_node),
                        (uint32_t)events.size(), false);
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
                      event.constraint, fold, event.rsan_bug_dir});
  }
  profile_stop(data, decode_start, &data->profile_decode_ns,
               &data->profile_decode_calls);
  uint64_t insert_start = profile_start(data);
  const uint64_t opaque_before = data->tree.num_opaque;
  uint32_t created = root_capture
      ? data->tree.InsertTrace(events, data->single_pass_label_info,
                               MAX_LABEL, buf, (uint32_t)buf_size,
                               out_tail_node, out_tail_dir)
      : data->tree.InsertSuffix(data->last_node, data->last_dir, events,
                                data->single_pass_label_info, MAX_LABEL, buf,
                                (uint32_t)buf_size, out_tail_node,
                                out_tail_dir);
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
  capture_structural_fault_if_any(
      data, events, data->single_pass_label_info, MAX_LABEL, buf, buf_size,
      root_capture ? "root-shm" : "shm-suffix",
      root_capture ? 0 : data->tree.depth(data->last_node), count, false);
  capture_opaque_if_new(data, opaque_before, events,
                        data->single_pass_label_info, MAX_LABEL, buf,
                        buf_size, root_capture ? "root-shm" : "shm-suffix",
                        root_capture ? 0 : data->tree.depth(data->last_node),
                        count, false);
  disarm_capture(data);
  return true;
}

static bool replay_pipe_suffix(my_mutator_t *data, const u8 *buf,
                               size_t buf_size, const char *fname,
                               pcbt::NodeRef node, uint8_t dir) {
  ProfileSegment replay_seg(data, &data->profile_replay_ns,
                            &data->profile_replay_calls);
  arm_pipe_suffix_capture(data, node, dir);
  // Testcase writes go through the MAIN fsrv (afl_fsrv_init_dup does not copy
  // the shmem_fuzz pointers); the run executes the concolic forkserver.
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), buf_size);
  fsrv_run_result_t result = afl_fsrv_run_target(concolic_fsrv(data),
      data->afl->fsrv_concolic.exec_tmout, &data->afl->stop_soon);
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
  // Testcase writes go through the MAIN fsrv (see replay_pipe_suffix); the
  // run executes the concolic forkserver.
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), buf_size);
  fsrv_run_result_t result = afl_fsrv_run_target(concolic_fsrv(data),
      data->afl->fsrv_concolic.exec_tmout, &data->afl->stop_soon);
  if (result != FSRV_RUN_OK) {
    WARNF("full-pipe replay failed for %s (%u)\n", fname, result);
    data->failed_runs += 1;
    disarm_capture(data);
    return false;
  }
  return insert_full_stream(data, buf, buf_size, fname);
}

// Execute the concolic forkserver once on the given candidate. The caller
// must have armed the capture (full/suffix/root) first; the child's event
// stream lands in the concolic fsrv's sym_trace_buf (or SHM) and is consumed
// by the caller. Testcase bytes are written through the MAIN fsrv (the dup'd
// secondary fsrvs share its out_file/shmem_fuzz).
static bool run_concolic_fsrv(my_mutator_t *data, const u8 *buf, size_t len,
                              const char *what) {
  afl_forkserver_t *cfsrv = concolic_fsrv(data);
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), len);
  ProfileSegment seg(data, &data->profile_exec_ns, &data->profile_exec_calls);
  fsrv_run_result_t result =
      afl_fsrv_run_target(cfsrv, cfsrv->exec_tmout, &data->afl->stop_soon);
  data->concolic_run_calls += 1;
  if (result != FSRV_RUN_OK) {
    WARNF("concolic run failed for %s (%u)\n", what, result);
    data->concolic_run_failed += 1;
    if (cfsrv->last_run_timed_out) data->trace_timeouts += 1;
    return false;
  }
  return true;
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

static void stash_closures(my_mutator_t *data, const std::string &fname,
                           std::vector<pcbt::AttachedClosure> &&cls) {
  if (!cls.empty()) {
    const auto &c0 = cls[0];
    fprintf(stderr, "[pcbt] attached closures=%zu s=", cls.size());
    for (size_t i = 0; i < c0.s.size() && i < 8; ++i)
      fprintf(stderr, "%s%u", i ? "," : "", c0.s[i]);
    fprintf(stderr, " node=%u %s\n", c0.node, fname.c_str());
  }
  data->closures_by_file[fname] = std::move(cls);
}

static void load_current_closures(my_mutator_t *data, const char *filename) {
  data->current_closures.clear();
  if (!filename) return;
  auto it = data->closures_by_file.find(filename);
  if (it != data->closures_by_file.end()) {
    data->current_closures = it->second;
    return;
  }
  std::vector<u8> buf;
  if (!read_queue_file(filename, &buf)) return;
  if (data->worker_mode) {
    auto wr = worker_check(&data->worker, buf.data(), (uint32_t)buf.size());
    stash_closures(data, filename, std::move(wr.closures));
  } else {
    std::vector<pcbt::AttachedClosure> cls;
    data->tree.collect_bug_closures(buf.data(), (uint32_t)buf.size(), &cls);
    stash_closures(data, filename, std::move(cls));
  }
  auto it2 = data->closures_by_file.find(filename);
  if (it2 != data->closures_by_file.end())
    data->current_closures = it2->second;
}

static char *save_probe_case(my_mutator_t *data, const u8 *buf, size_t len,
                             uint8_t veto_kind) {
  const char *dir = veto_kind == 0 ? data->probe_terminal_dir
                                   : data->probe_rlimit_dir;
  if (!dir) return nullptr;
  char *path = alloc_printf("%s/probe-%06llu", dir,
                            (unsigned long long)data->probe_case_seq++);
  int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
  if (fd < 0) {
    PFATAL("cannot create probe case %s", path);
  }
  ck_write(fd, buf, len, path);
  close(fd);
  return path;
}

// The bootstrap input is AFL's candidate file; replay validation needs its
// real bytes and length (Len nodes evaluate against the candidate length, so
// a null buffer / zero length mispredicts length-boundary predicates).
// Prefer fsrv.out_file (correct under AFL_TMPDIR); fall back to
// <out_dir>/.cur_input for the common default layout.
static bool read_cur_input(my_mutator_t *data, std::vector<u8> *buf) {
  if (data->afl->fsrv.out_file && *data->afl->fsrv.out_file) {
    if (read_queue_file((const char *)data->afl->fsrv.out_file, buf)) {
      return true;
    }
  }
  if (!data->afl->out_dir) return false;
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
  if ((!data->pair_log && !data->forensics_dir) ||
      tail_node == pcbt::kUnexplored) return;
  std::vector<u8> buf;
  if (!read_cur_input(data, &buf)) return;
  if (data->pair_log) {
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

// Sanitizer crash forensics: the sanitizer forkserver re-executes every
// coverage-gaining candidate to catch memory-safety bugs. The sanitizer
// binary is built with AFL_SAN_NO_INST (no coverage writes), so a nonzero
// run result here is a genuine sanitizer report. Per-signal dedup v1: the
// first crash per signal is saved to crashes/, repeats only bump counters.
static void handle_san_crash(my_mutator_t *data, const u8 *buf, size_t len) {
  afl_forkserver_t *sfsrv = &data->afl->fsrv_san;
  int sig = 0;
  if (sfsrv->child_status != -1 && WIFSIGNALED(sfsrv->child_status)) {
    sig = WTERMSIG(sfsrv->child_status);
  }
  data->san_crashes += 1;
  auto it = data->san_crash_sig_counts.find(sig);
  if (it == data->san_crash_sig_counts.end()) {
    it = data->san_crash_sig_counts.emplace(sig, 0).first;
  }
  uint64_t seen = it->second;
  it->second += 1;
  if (seen > 0 || !data->afl->out_dir) return;
  char *path = alloc_printf("%s/crashes/id:%06llu,sig:%02u,san",
                            data->afl->out_dir,
                            (unsigned long long)data->san_crash_seq++, sig);
  int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
  if (fd < 0) {
    PFATAL("cannot create sanitizer crash case %s", path);
  }
  ck_write(fd, const_cast<u8 *>(buf), len, path);
  close(fd);
  data->san_crashes_saved += 1;
  WARNF("sanitizer crash saved: %s (sig=%d)\n", path, sig);
  ck_free(path);
}

extern "C" void afl_custom_post_run(my_mutator_t *data) {
  // Probe diagnostic: classify what a sampled vetoed candidate executed past
  // the known terminal prefix. Nonempty suffix = screening defect (the tree
  // claimed the decision trace terminates, but it does not).
  if (data->last_was_probe && data->single_pass_armed) {
    uint32_t probe_mode = __atomic_load_n(&data->single_pass_control->mode,
                                          __ATOMIC_ACQUIRE);
    // Replay-all veto coverage: every vetoed candidate ran under FULL
    // capture; validate its complete event stream against the tree. A
    // cid/direction mismatch means the veto path itself disagrees with the
    // candidate's actual stream; an after_terminal error means the
    // candidate carried events past a tree terminal — both are
    // symbolic-decision-event omission signals. The stream is never
    // inserted (probes do not grow the tree); mismatches mark the reached
    // node unstable so later candidates are not screened against a
    // self-contradictory model.
    if (data->replay_all && probe_mode == SYMAFL_TRACE_FULL_STREAM) {
      std::vector<u8> buf;
      if (read_cur_input(data, &buf)) {
        if (data->tree.conflict_diag()) {
          size_t fshown = buf.size() < 16 ? buf.size() : 16;
          fprintf(stderr,
                  "[pcbt-replay] veto forensics cur_input_len=%zu "
                  "pipe_bytes=%zu hex=",
                  buf.size(), concolic_fsrv(data)->sym_trace_len);
          for (size_t k = 0; k < fshown; ++k)
            fprintf(stderr, "%02x", buf[k]);
          fprintf(stderr, "\n");
        }
        // The probe executed the CONCRETE target on the main fsrv; the armed
        // capture is empty. Materialize the vetoed candidate's full stream by
        // executing the concolic forkserver now.
        if (run_concolic_fsrv(data, buf.data(), buf.size(),
                              "replay-all-veto")) {
          std::vector<pcbt::Event> events;
          if (decode_pipe_events(data, &events, "replay-all-veto")) {
            (void)replay_check_trace(data, events, buf.data(), buf.size(),
                                     "replay-all-veto", false);
          }
        }
      }
      disarm_capture(data);
      return;
    }
    if (!data->probe_diag) {
      if (!data->probe_capture_pending) disarm_capture(data);
      return;
    }
    // Same as above: the concrete probe run produced no capture, so execute
    // the concolic forkserver (suffix capture armed at post_process) to
    // classify what the vetoed candidate does past the terminal prefix.
    {
      std::vector<u8> buf;
      if (!read_cur_input(data, &buf) ||
          !run_concolic_fsrv(data, buf.data(), buf.size(), "probe-diag")) {
        if (!data->probe_capture_pending) disarm_capture(data);
        return;
      }
    }
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
    // Replay-all quality mode: validate EVERY admitted run's full stream
    // against the current tree, not only coverage-gaining runs. This is the
    // census for symbolic-decision-event omissions: cid/direction mismatches
    // mark the reached node unstable and are counted, and an
    // after_terminal error means a later candidate carried events past a
    // terminal that an earlier (empty-suffix) run closed. The capture stays
    // armed so queue_new_entry can still insert a gaining run's suffix; the
    // insert skips the duplicate replay via replay_run_done.
    if (data->replay_all && data->single_pass_armed &&
        data->last_node != pcbt::kUnexplored) {
      data->replay_run_done = false;
      uint32_t mode = __atomic_load_n(&data->single_pass_control->mode,
                                      __ATOMIC_ACQUIRE);
      if (mode == SYMAFL_TRACE_FULL_STREAM) {
        std::vector<u8> buf;
        if (read_cur_input(data, &buf)) {
          // The admitted candidate just ran CONCRETE on the main fsrv; the
          // armed capture is empty. Execute the concolic forkserver to
          // materialize its full stream for tree validation.
          if (run_concolic_fsrv(data, buf.data(), buf.size(), "replay-all")) {
            std::vector<pcbt::Event> events;
            if (decode_pipe_events(data, &events, "replay-all")) {
              if (data->tree.conflict_diag()) {
                // skipCnt hypothesis: if the tree's suffix start position
                // (skip_for) exceeds the candidate's actual event count, a
                // steady-state suffix capture would be empty and the empty
                // suffix would close a (possibly fake) terminal. Print the
                // comparison for every admitted run while diagnosing.
                uint32_t skip_for =
                    data->last_node != pcbt::kUnexplored
                        ? data->tree.skip_for(data->last_node, data->last_dir)
                        : 0;
                uint64_t ev_total = 0;
                for (const pcbt::Event &ev : events) ev_total += ev.count;
                fprintf(stderr,
                        "[pcbt-replay] admit skipcnt node=%u dir=%u "
                        "skip_for=%u events=%zu expanded=%llu\n",
                        data->last_node, data->last_dir, skip_for,
                        events.size(), (unsigned long long)ev_total);
              }
              (void)replay_check_trace(data, events, buf.data(), buf.size(),
                                       "replay-all", false);
              data->replay_run_done = true;
            }
          }
        }
      }
    }
    // Admitted-run diagnostic: does the frontier suffix carry decisions
    // (tree gain) even when the run gains no bitmap coverage? Also needs the
    // concolic execution (the concrete run produced no capture). A gaining
    // candidate here pays one concolic run total: queue_new_entry consumes
    // replay_run_done and inserts from the same capture.
    if (data->probe_diag && data->single_pass_armed &&
        data->last_node != pcbt::kUnexplored) {
      std::vector<u8> buf;
      if (read_cur_input(data, &buf) &&
          run_concolic_fsrv(data, buf.data(), buf.size(), "admit-diag")) {
        classify_suffix(data, &data->diag_admit_suffix_empty,
                        &data->diag_admit_suffix_nonempty,
                        &data->diag_admit_suffix_overflow,
                        &data->diag_admit_suffix_events);
        data->replay_run_done = true;
      }
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
  // Bootstrap: the initial corpus entries are inserted into the tree at the
  // first afl_custom_queue_get (the concolic forkserver does not exist before
  // that; queue_new_entry buffers the seed names). The runs that reach this
  // branch are concrete dry-run/calibration executions on the main fsrv —
  // their armed capture is empty and must be disarmed WITHOUT insertion (an
  // empty full stream would otherwise close tree edges with no evidence).
  if (data->single_pass_armed) disarm_capture(data);
  data->last_node = pcbt::kUnexplored;
}

extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  // Forkserver is up by the first queue_get. Drop the parent's write end so
  // only the target forkserver/children hold it. Keeping it open in afl-fuzz
  // prevents EOF on the read side and is a common source of incomplete
  // post-status drains under load.
  if (data->full_stream_write_fd >= 0) {
    close(data->full_stream_write_fd);
    data->full_stream_write_fd = -1;
  }
  // Init-time seed flush: read_testcases queued the seeds while the concolic
  // forkserver did not exist (queue_new_entry buffered their names in
  // pending_seeds). Run each seed through the concolic forkserver now — it is
  // up by the first queue_get — and insert its full stream into the tree so
  // the SEDBT is ready before the first post_process. last_gained is set per
  // seed so the run that follows this queue_get does not misattribute a
  // non-gain to the flushed seed's frontier edge.
  if (!data->seeds_flushed) {
    data->seeds_flushed = true;
    if (data->worker_mode) {
      if (!worker_wait_tree_ready(&data->worker)) {
        FATAL("worker TREE_READY failed");
      }
      for (const std::string &seed : data->pending_seeds) {
        std::vector<u8> buf;
        if (!read_queue_file(seed.c_str(), &buf)) continue;
        auto wr = worker_check(&data->worker, buf.data(), (uint32_t)buf.size());
        data->worker.learned[seed] = wr.learned;
        stash_closures(data, seed, std::move(wr.closures));
        fprintf(stderr, "[pcbt] worker seed learned=%u %s\n", wr.learned,
                seed.c_str());
      }
      data->pending_seeds.clear();
      if (!worker_ack(&data->worker) || !worker_wait_done(&data->worker)) {
        FATAL("worker bootstrap ACK/DONE failed");
      }
    } else if (data->screening) {
      for (const std::string &seed : data->pending_seeds) {
        std::vector<u8> buf;
        if (!read_queue_file(seed.c_str(), &buf)) {
          WARNF("cannot read bootstrap seed %s\n", seed.c_str());
          data->failed_runs += 1;
          continue;
        }
        arm_full_capture(data);
        if (!run_concolic_fsrv(data, buf.data(), buf.size(),
                               "bootstrap-seed")) {
          disarm_capture(data);
          data->last_gained = false;
          data->failed_runs += 1;
          continue;
        }
        pcbt::NodeRef tail_node = pcbt::kUnexplored;
        uint8_t tail_dir = 0;
        if (!insert_full_stream(data, buf.data(), buf.size(), seed.c_str(),
                                &tail_node, &tail_dir)) {
          data->last_gained = false;
          data->failed_runs += 1;
          continue;
        }
        data->traced_entries.insert(seed);
        record_admitted_pair(data, tail_node, tail_dir);
        data->last_gained = true;
        std::vector<pcbt::AttachedClosure> cls;
        data->tree.collect_bug_closures(buf.data(), (uint32_t)buf.size(), &cls);
        stash_closures(data, seed, std::move(cls));
      }
      data->pending_seeds.clear();
    }
  }
  data->bootstrap_done = true;
  if (data->concolic_deadline && !data->phase_start) {
    data->phase_start = time(nullptr);
  }
  load_current_closures(data, filename ? (const char *)filename : nullptr);
  return 1;
}

// AFL++ calls this before its normal save/queue path for a SymAFL probe. The
// probe result is measured against a temporary virgin bitmap in AFL++, then
// retained outside the queue for replay diagnostics. It never updates the
// PCBT, AFL virgin_bits, scheduler queue, or admitted-gain counters.
extern "C" void afl_custom_probe_result(my_mutator_t *data, const u8 *buf,
                                         size_t buf_size, u8 new_bits) {
  if (getenv("SYMAFL_MUTATOR_QUEUE_DIAG")) {
    fprintf(stderr,
            "[mutator-probe] marker=%u kind=%u new_bits=%u len=%zu pending=%u\n",
            data->last_was_probe ? 1u : 0u,
            (unsigned)data->afl->pcbt_candidate_kind, new_bits, buf_size,
            data->probe_capture_pending ? 1u : 0u);
  }
  if (!data->last_was_probe) return;

  char *probe_path = nullptr;
  if (new_bits) {
    probe_path = save_probe_case(data, buf, buf_size,
                                 data->last_probe_veto_kind);
    if (!probe_path) FATAL("probe case directory is not initialized");
    data->veto_probe_gained += 1;
    if (data->last_probe_veto_kind == 0) {
      data->probe_gained_terminal += 1;
      WARNF("terminal-veto-but-gain detected; stopping quality run\n");
      request_residual_abort(data, "terminal_veto_but_gain");
      data->afl->stop_soon = 1;
      if (data->forensics_dir) {
        std::vector<pcbt::Event> events;
        uint32_t raw_event_count = 0;
        bool trace_overflow = false;
        decode_probe_capture(data, &events, &raw_event_count,
                             &trace_overflow);
        const uint32_t mode = data->single_pass_armed
            ? __atomic_load_n(&data->single_pass_control->mode,
                              __ATOMIC_ACQUIRE)
            : SYMAFL_TRACE_OFF;
        const char *trace_mode = mode == SYMAFL_TRACE_SUFFIX_SHM
            ? "shm-suffix"
            : mode == SYMAFL_TRACE_SUFFIX_PIPE ? "pipe-suffix" : "none";
        ForensicSnapshotMeta meta;
        meta.trace_mode = trace_mode;
        meta.skip_depth = data->last_veto_depth;
        meta.raw_event_count = raw_event_count;
        meta.trace_overflow = trace_overflow;
        meta.veto_node = data->last_veto_node;
        meta.veto_dir = data->last_veto_dir;
        meta.veto_kind = data->last_probe_veto_kind;
        meta.veto_depth = data->last_veto_depth;
        meta.new_bits = new_bits;
        meta.pair_log = data->pair_log_path;
        capture_forensic_snapshot(data, "terminal-veto-but-gain", events,
                                  __dfsan_label_info, MAX_LABEL, buf, buf_size,
                                  meta);
      }
    } else if (data->last_probe_veto_kind == 2) {
      // Unstable-prefix veto with probe coverage gain is NOT TVBG: the tree
      // already marked the prefix unsafe. Do not stop the quality run as a
      // terminal residual (kind 0). Log for supporting diagnostics only.
      fprintf(stderr,
              "[pcbt] unstable-veto-probe-gain node=%u dir=%u depth=%u "
              "new_bits=%u (not TVBG)\n",
              data->last_veto_node, data->last_veto_dir, data->last_veto_depth,
              new_bits);
    } else {
      data->probe_gained_rlimit += 1;
      // Probe learn: a vetoed candidate that gains coverage proves the
      // frontier edge still pays out. Insert its captured suffix into the
      // tree and refresh the edge's retry budget so subsequent candidates
      // on the same edge can reach that coverage instead of being vetoed at
      // the exhausted budget. Non-gaining probes never mutate the tree, so
      // non_gain_filter is preserved.
      if (data->probe_learn && data->probe_capture_pending &&
          data->probe_capture_node != pcbt::kUnexplored &&
          data->last_probe_suffix_nonempty) {
        std::vector<pcbt::Event> events;
        uint32_t raw_event_count = 0;
        bool trace_overflow = false;
        decode_probe_capture(data, &events, &raw_event_count,
                             &trace_overflow);
        if (!trace_overflow && !events.empty()) {
          uint32_t created = data->tree.InsertSuffix(
              data->probe_capture_node, data->probe_capture_dir, events,
              __dfsan_label_info, MAX_LABEL, buf, (uint32_t)buf_size, nullptr,
              nullptr);
          capture_structural_fault_if_any(
              data, events, __dfsan_label_info, MAX_LABEL, buf, buf_size,
              "probe-learn-suffix", data->tree.depth(data->probe_capture_node),
              raw_event_count, trace_overflow);
          if (created > 0) {
            // A nonempty learned suffix proves the edge has real follow-up
            // paths; refresh the budget so later candidates can reach them.
            // Empty-suffix gains are un-symbolized coverage differences and
            // are NOT learned: refreshing there admitted 8.6x more no-ops
            // (non_gain_filter 0.92 -> 0.12 in the libtiff experiment).
            data->tree.retry_count(data->probe_capture_node,
                                   data->probe_capture_dir) = 0;
            data->probe_learned += 1;
          }
        }
      }
    }
    if (data->probe_gained_log) {
      fprintf(data->probe_gained_log,
              "kind=%u node=%u dir=%u %s suffix=%s\n",
              data->last_probe_veto_kind, data->last_veto_node,
              data->last_veto_dir, probe_path,
              data->last_probe_suffix_nonempty
                  ? "nonempty"
                  : data->last_probe_suffix_overflow ? "overflow" : "empty");
      fflush(data->probe_gained_log);
    }
    record_veto_probe_pair(data, probe_path);
    if (data->sat_window) data->sat_probe_gained += 1;
    if (data->probe_diag) {
      if (data->last_probe_suffix_nonempty) data->probe_gained_nonempty += 1;
      else if (data->last_probe_suffix_overflow)
        data->probe_gained_overflow += 1;
      else
        data->probe_gained_empty += 1;
      fprintf(stderr,
              "[pcbt-diag] gained-case probe file=%s len=%zu veto_depth=%u "
              "veto_node=%u veto_cid=%u veto_dir=%u veto_kind=%u suffix=%s\n",
              probe_path, buf_size, data->last_veto_depth,
              data->last_veto_node,
              data->last_veto_node != pcbt::kUnexplored
                  ? data->tree.cid_of(data->last_veto_node)
                  : 0u,
              data->last_veto_dir, data->last_probe_veto_kind,
              data->last_probe_suffix_nonempty
                  ? "nonempty"
                  : data->last_probe_suffix_overflow ? "overflow" : "empty");
    }
  }

  // Probe capture is diagnostic only. In particular, SYMAFL_PROBE_LEARN must
  // not turn a measurement probe into a PCBT mutation or a future admit.
  data->probe_capture_pending = false;
  data->probe_capture_node = pcbt::kUnexplored;
  if (data->single_pass_armed) disarm_capture(data);
  data->last_probe_suffix_overflow = false;
  data->last_was_probe = false;
  data->last_gained = false;
  if (probe_path) ck_free(probe_path);
}

extern "C" u8 afl_custom_queue_new_entry(my_mutator_t *data,
                                         const u8 *filename_new_queue,
                                         const u8 *filename_orig_queue) {
  (void)filename_orig_queue;
  if (getenv("SYMAFL_MUTATOR_QUEUE_DIAG")) {
    fprintf(stderr,
            "[mutator-queue] marker=%u bootstrap=%u screening=%u fname=%s\n",
            data->last_was_probe ? 1u : 0u, data->bootstrap_done ? 1u : 0u,
            data->screening ? 1u : 0u,
            filename_new_queue ? (const char *)filename_new_queue : "(null)");
  }
  // Probe results are consumed by afl_custom_probe_result before AFL creates a
  // queue entry. Keep this defensive branch inert if an older AFL++ callback
  // path invokes queue_new_entry unexpectedly.
  if (data->last_was_probe) {
    data->last_was_probe = false;
    data->probe_capture_pending = false;
    data->probe_capture_node = pcbt::kUnexplored;
    if (data->single_pass_armed) disarm_capture(data);
    return 0;
  }
  // Init-time seed batch: read_testcases runs before the concolic forkserver
  // exists, so record the seed names here and flush them into the tree at the
  // first afl_custom_queue_get.
  if (!data->bootstrap_done) {
    if ((data->screening || data->worker_mode) && filename_new_queue) {
      data->pending_seeds.push_back((const char *)filename_new_queue);
    }
    return 0;
  }
  const char *fname = (const char *)filename_new_queue;
  std::vector<u8> buf;
  if (!read_queue_file(fname, &buf)) {
    WARNF("cannot read coverage-gaining queue entry %s\n", fname);
    disarm_capture(data);
    data->last_gained = false;
    data->failed_runs += 1;
    return 0;
  }
  bool committed = false;
  if (data->worker_mode) {
    auto wr = worker_check(&data->worker, buf.data(), (uint32_t)buf.size());
    data->worker.learned[fname] = wr.learned;
    stash_closures(data, fname, std::move(wr.closures));
    if (wr.learned == symafl::kUnlearned) {
      if (!worker_submit(&data->worker, wr.frontier, wr.dir, wr.skip_cnt,
                         buf.data(), (uint32_t)buf.size())) {
        fprintf(stderr, "[pcbt] worker ring full, learned=0 %s\n", fname);
      }
    }
    committed = true;
  } else if (data->screening) {
    if (data->replay_run_done) {
      data->replay_run_done = false;  // post_run already ran the fsrv
    } else if (data->single_pass_armed) {
      if (!run_concolic_fsrv(data, buf.data(), buf.size(), fname)) {
        disarm_capture(data);
        data->last_gained = false;
        data->failed_runs += 1;
        return 0;
      }
    } else {
      data->last_gained = false;
      data->failed_runs += 1;
      WARNF("coverage-gaining admitted entry has no trace capture: %s\n",
            fname);
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
    committed = inserted;
    if (!inserted && root_capture) {
      committed = replay_full_capture(data, buf.data(), buf.size(), fname);
    } else if (!inserted && node != pcbt::kUnexplored) {
      committed = replay_pipe_suffix(data, buf.data(), buf.size(), fname, node,
                                     dir);
    }
    if (committed) {
      if (data->admitted_gained_log) {
        fprintf(data->admitted_gained_log, "node=%u dir=%u root=%u %s\n",
                data->last_node, data->last_dir,
                data->root_shm_capture ? 1u : 0u, filename_new_queue);
        fflush(data->admitted_gained_log);
      }
        data->traced_entries.insert((const char *)filename_new_queue);
        record_admitted_pair(data, tail_node, tail_dir);
        std::vector<pcbt::AttachedClosure> cls;
        data->tree.collect_bug_closures(buf.data(), (uint32_t)buf.size(), &cls);
        stash_closures(data, fname, std::move(cls));
    } else {
      WARNF("coverage-gaining admitted entry was not inserted: %s\n", fname);
    }
  }
  data->last_gained = committed;
  // SANITIZER STAGE: every coverage-gaining candidate (screening or not) is
  // re-executed on the sanitizer forkserver to catch memory-safety bugs.
  // Crashes are saved by the mutator; timeouts are counted only.
  if (data->afl->fsrv_san.fsrv_pid > 0) {
    afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf.data()),
                               buf.size());
    fsrv_run_result_t sres = afl_fsrv_run_target(
        &data->afl->fsrv_san, data->afl->fsrv_san.exec_tmout,
        &data->afl->stop_soon);
    data->san_run_calls += 1;
    if (sres == FSRV_RUN_CRASH) {
      handle_san_crash(data, buf.data(), buf.size());
    } else if (sres == FSRV_RUN_TMOUT) {
      data->san_tmouts += 1;
    }
  }
  return 0;
}

/// PCBT screening: veto mutated candidates that cannot reach an unexplored
/// frontier. Returning 0 with *out_buf=NULL tells AFL++ to skip executing
/// this candidate entirely.
extern "C" size_t afl_custom_post_process(my_mutator_t *data, u8 *buf,
                                          size_t buf_size, u8 **out_buf) {
  data->profile_exec_armed = false;
  // Candidate kind is valid only for the current post_process decision.
  data->afl->pcbt_probe_active = 0;
  data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_NONE;
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
  // Defensive: a stale replay-all marker (queue_new_entry never consumed it)
  // must not suppress the next run's replay.
  data->replay_run_done = false;
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
              "screening off (concolic stage disabled, sanitizer continues)\n",
              (unsigned long long)data->concolic_deadline);
      data->screening = false;
    }
  }

  if (!data->screening) {
    data->screened += 1;
    data->admitted += 1;
    data->profile_exec_armed = data->profile_enabled;
    data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  // ADR 0010 W1: the worker owns capture + insert. Admit every concrete
  // candidate; CheckInput on the live SHM happens in queue_new_entry.
  if (data->worker_mode) {
    data->screened += 1;
    data->admitted += 1;
    data->profile_exec_armed = data->profile_enabled;
    data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
    data->vetoes_since_admit = 0;
    data->last_gained = false;
    data->last_node = pcbt::kUnexplored;
    data->last_dir = 0;
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  // Production default (ADR 0009): admit every candidate, arm a complete
  // stream, keep learning. No CheckInput frontier, so InsertSuffix is
  // invalid — last_node stays unexplored and queue_new_entry uses InsertTrace.
  if (!data->veto_enabled) {
    data->screened += 1;
    data->admitted += 1;
    data->profile_exec_armed = data->profile_enabled;
    data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
    data->vetoes_since_admit = 0;
    data->last_gained = false;
    data->last_node = pcbt::kUnexplored;
    data->last_dir = 0;
    arm_full_capture(data);
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  data->screened += 1;
  pcbt::NodeRef node = pcbt::kUnexplored;
  uint8_t dir = 0;
  bool admitted = check_input_timed(data, buf, (uint32_t)buf_size, &node, &dir,
                                    &data->last_veto_depth,
                                    &data->last_veto_node,
                                    &data->last_veto_dir,
                                    &data->last_veto_kind);
  if (admitted) {
    data->profile_exec_armed = data->profile_enabled;
    data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
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
  // kind 0=terminal (TVBG class), 1=rlimit, 2=unstable (not TVBG).
  data->afl->pcbt_candidate_kind =
      data->last_veto_kind == 0 ? PCBT_CANDIDATE_VETO_TERMINAL
                                : PCBT_CANDIDATE_VETO_RLIMIT;
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
  // With SYMAFL_REPLAY_ALL every vetoed candidate is probed under FULL
  // capture so its complete event stream can be replayed against the tree:
  // a mismatch or an after_terminal error on a vetoed stream is an omission
  // signal (the veto itself was based on a tree that disagrees with the
  // candidate's actual stream).
  bool replay_all_probe = data->replay_all;
  if (replay_all_probe ||
      (data->veto_probe_every &&
       ++data->veto_probe_count >= data->veto_probe_every)) {
    if (data->veto_probe_every) data->veto_probe_count = 0;
    data->veto_probe_admitted += 1;
    data->last_was_probe = true;
    data->afl->pcbt_probe_active = 1;
    data->last_gained = false;
    data->last_node = pcbt::kUnexplored;
    data->last_probe_veto_kind = data->last_veto_kind;
    data->last_probe_suffix_nonempty = false;
    data->last_probe_len = (uint32_t)buf_size;
    data->last_probe_input_len = (uint32_t)buf_size < 64 ? (uint32_t)buf_size : 64;
    memcpy(data->last_probe_input, buf, data->last_probe_input_len);
    if (data->sat_window) data->sat_probe_total += 1;
    if (data->single_pass_armed) disarm_capture(data);
    if (data->replay_all) {
      // Full-stream capture for the vetoed candidate's complete replay.
      arm_full_capture(data);
      // Replay-all diagnostic: persist every vetoed probe input so the
      // truncated/empty-stream cases can be replayed outside AFL and
      // compared with the in-run capture.
      if (data->probe_case_dir) {
        char *veto_path = alloc_printf("%s/veto-%llu.bin",
                                       data->probe_case_dir,
                                       (unsigned long long)data->vetoed);
        FILE *vf = fopen(veto_path, "wb");
        if (vf) {
          fwrite(buf, 1, buf_size, vf);
          fclose(vf);
        }
        ck_free(veto_path);
      }
      // Probe capture is not an admitted candidate: do not let the normal
      // post_run retry bookkeeping treat it as last_node/last_dir.
      data->last_node = pcbt::kUnexplored;
      data->probe_capture_pending = false;
      data->probe_capture_node = pcbt::kUnexplored;
    } else {
      const bool forensic_terminal_capture =
          data->forensics_dir && data->last_probe_veto_kind == 0 &&
          data->last_veto_depth > 0;
      if ((data->probe_diag || forensic_terminal_capture) &&
          data->last_veto_depth > 0) {
        arm_suffix_capture(data, data->last_veto_node, data->last_veto_dir);
        data->probe_capture_pending =
            (data->probe_learn && data->last_probe_veto_kind == 1) ||
            forensic_terminal_capture;
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
                "screening off (concolic stage disabled, sanitizer continues)\n",
                (unsigned long long)data->vetoed,
                (unsigned long long)data->sat_window,
                (unsigned long long)data->sat_min_gains,
                (unsigned long long)data->sat_low_windows,
                data->phase_start
                    ? (unsigned long long)(time(nullptr) - data->phase_start)
                    : 0ull);
      }
      data->screening = false;
    }
  }
  // A saturated PCBT is a phase boundary, not a local screening fallback:
  // the main forkserver already runs the concrete target, so nothing is
  // switched or restarted — the concolic stage simply stops being fed.
  if (data->tree.IsSaturated(data->rlimit, data->len_rlimit)) {
    data->screening = false;
    if (!data->saturation_logged) {
      data->saturation_logged = true;
      fprintf(stderr,
              "[pcbt] tree saturated after %llu vetoes "
              "(phase_secs=%llu); screening off (concolic stage disabled, "
              "sanitizer continues)\n",
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
           "tautology=%llu failed=%llu timeouts=%llu memerr=%llu "
           "screened=%llu admitted=%llu vetoed=%llu traced_entries=%llu saturated=%llu "
           "single_pass=%llu single_pass_overflow=%llu "
           "admit_empty=%llu admit_opaque=%llu follow_tautology=%llu admit_eval_failure=%llu admit_frontier=%llu admit_unstable=%llu "
           "admit_len_veto=%llu veto_terminal=%llu veto_rlimit=%llu veto_unstable=%llu probe_admitted=%llu probe_gained=%llu "
           "probe_gained_terminal=%llu probe_gained_rlimit=%llu profile=%d "
           "concolic_runs=%llu concolic_failed=%llu "
           "san_runs=%llu san_tmouts=%llu san_crashes=%llu san_saved=%llu "
           "check_ns=%llu check_calls=%llu trace_ns=%llu trace_calls=%llu "
           "replay_ns=%llu replay_calls=%llu exec_ns=%llu exec_calls=%llu",
           (unsigned long long)t.num_traces, (unsigned long long)t.num_nodes,
           (unsigned long long)t.num_pred_nodes(),
           (unsigned long long)t.max_depth,
           (unsigned long long)t.num_conflicts,
           (unsigned long long)t.num_opaque,
           (unsigned long long)t.num_tautology,
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
           (unsigned long long)t.check_follow_tautology,
           (unsigned long long)t.check_admit_eval_failure,
           (unsigned long long)t.check_admit_frontier,
           (unsigned long long)t.check_admit_unstable,
           (unsigned long long)t.check_admit_len_veto,
           (unsigned long long)t.check_veto_terminal,
           (unsigned long long)t.check_veto_rlimit,
           (unsigned long long)t.check_veto_unstable,
           (unsigned long long)data->veto_probe_admitted,
           (unsigned long long)data->veto_probe_gained,
           (unsigned long long)data->probe_gained_terminal,
           (unsigned long long)data->probe_gained_rlimit,
           (int)(data->profile_enabled ? 1 : 0),
           (unsigned long long)data->concolic_run_calls,
           (unsigned long long)data->concolic_run_failed,
           (unsigned long long)data->san_run_calls,
           (unsigned long long)data->san_tmouts,
           (unsigned long long)data->san_crashes,
           (unsigned long long)data->san_crashes_saved,
           (unsigned long long)data->profile_check_ns,
           (unsigned long long)data->profile_check_calls,
           (unsigned long long)data->profile_trace_ns,
           (unsigned long long)data->profile_trace_calls,
           (unsigned long long)data->profile_replay_ns,
           (unsigned long long)data->profile_replay_calls,
           (unsigned long long)data->profile_exec_ns,
           (unsigned long long)data->profile_exec_calls);
  return buf;
}
