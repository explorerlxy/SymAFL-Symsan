/*
  SymAFL v2 custom mutator for AFL++: PCBT-guided seed screening.

  Based on the SymSan AFL++ driver
  (c) 2023 - 2024 by Chengyu Song <csong@ucr.edu>, Apache 2.0.

  v2 strips the solving chain (no TaskManager / Solver / custom mutations).
  ADR 0010: this mutator is the concrete fuzzer side. Concolic + SEDBT
  insert live in symafl-worker. The mutator admits every concrete candidate
  (ADR 0009), submits LearnJobs on coverage gain, and optionally re-executes
  gainers on the sanitizer forkserver. Focused mutation uses RSan closures
  from the live tree SHM.
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

// Worker bootstrap InsertTrace is pipe-full. Steady-state LearnJobs use
// suffix capture inside symafl-worker, not this process.

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
  // Optional sanitizer forkserver (SYMAFL_SANITIZER_TARGET), spawned by AFL++.
  char *sanitizer_target = nullptr;
  // Init-time queue_new_entry batch: read_testcases runs before TREE_READY,
  // so seed names are queued here and CheckInput'd at first queue_get.
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

  // ADR 0010: the CLI target is the concrete binary. Concolic belongs to
  // symafl-worker (SYMAFL_WORKER_SOCK required). Optional sanitizer
  // forkserver is spawned by AFL++ after this init returns.
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
  const char *wsock = getenv("SYMAFL_WORKER_SOCK");
  if (!wsock || !*wsock) {
    FATAL("PCBT mode requires SYMAFL_WORKER_SOCK "
          "(concolic is symafl-worker; ADR 0010)");
  }
  data->worker_mode = true;
  if (!worker_connect(&data->worker, wsock)) {
    FATAL("SYMAFL_WORKER_SOCK connect failed: %s", wsock);
  }
  fprintf(stderr, "[pcbt] worker client connected (%s)\n", wsock);

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
            "[pcbt] no-veto: CheckInput is a learn-gate on the worker, "
            "not a concrete veto (ADR 0009 / 0010)\n");
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
  if (data->worker.tree) {
    fprintf(stderr, "[pcbt] worker_shm nodes=%u preds=%u\n",
            data->worker.tree->hdr.n_nodes.load(std::memory_order_acquire),
            data->worker.tree->hdr.n_preds.load(std::memory_order_acquire));
  }
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
  auto wr = worker_check(&data->worker, buf.data(), (uint32_t)buf.size());
  stash_closures(data, filename, std::move(wr.closures));
  auto it2 = data->closures_by_file.find(filename);
  if (it2 != data->closures_by_file.end())
    data->current_closures = it2->second;
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
  (void)data;
}

extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  if (!data->seeds_flushed) {
    data->seeds_flushed = true;
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
  (void)data;
  (void)buf;
  (void)buf_size;
  (void)new_bits;
}

extern "C" u8 afl_custom_queue_new_entry(my_mutator_t *data,
                                         const u8 *filename_new_queue,
                                         const u8 *filename_orig_queue) {
  (void)filename_orig_queue;
  if (!data->bootstrap_done) {
    if (filename_new_queue) {
      data->pending_seeds.push_back((const char *)filename_new_queue);
    }
    return 0;
  }
  const char *fname = (const char *)filename_new_queue;
  std::vector<u8> buf;
  if (!read_queue_file(fname, &buf)) {
    WARNF("cannot read coverage-gaining queue entry %s\n", fname);
    data->last_gained = false;
    data->failed_runs += 1;
    return 0;
  }
  auto wr = worker_check(&data->worker, buf.data(), (uint32_t)buf.size());
  data->worker.learned[fname] = wr.learned;
  stash_closures(data, fname, std::move(wr.closures));
  if (wr.learned == symafl::kUnlearned) {
    if (!worker_submit(&data->worker, wr.frontier, wr.dir, wr.skip_cnt,
                       buf.data(), (uint32_t)buf.size())) {
      fprintf(stderr, "[pcbt] worker ring full, learned=0 %s\n", fname);
    }
  }
  data->last_gained = true;
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
  data->afl->pcbt_probe_active = 0;
  data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_NONE;
  data->last_was_probe = false;
  data->replay_run_done = false;
  data->last_node = pcbt::kUnexplored;

  if (!data->screening) {
    data->screened += 1;
    data->admitted += 1;
    data->profile_exec_armed = data->profile_enabled;
    data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
    write_progress(data, false);
    *out_buf = buf;
    return buf_size;
  }

  data->screened += 1;
  data->admitted += 1;
  data->profile_exec_armed = data->profile_enabled;
  data->afl->pcbt_candidate_kind = PCBT_CANDIDATE_ADMIT;
  data->vetoes_since_admit = 0;
  data->last_gained = false;
  data->last_dir = 0;
  write_progress(data, false);
  *out_buf = buf;
  return buf_size;
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
