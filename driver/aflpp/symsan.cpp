/*
  SymAFL v2 custom mutator for AFL++: SEDBT-guided seed screening.

  Based on the SymSan AFL++ driver
  (c) 2023 - 2024 by Chengyu Song <csong@ucr.edu>, Apache 2.0.

  v2 strips the solving chain (no TaskManager / Solver / custom mutations).
  ADR 0010: this mutator is the concrete fuzzer side. Concolic + SEDBT
  insert live in symafl-analyzer. CheckInput is a learn-gate (ADR 0009).
  Path-s mutants that replay the parent seed's LearnJob suffix skip concrete
  (SYMAFL_PATH_S_SCREEN); havoc never skips. An explore mutant that
  changed a tainted GEP-index pin (not indcall/read-length) skips fsrv_cov
  and runs fsrv_san (SYMAFL_PATH_S_CONS_SAN) once per distinct GEP-byte
  tuple; later mutants with the same GEP value go through cov.
  Coverage gainers submit
  LearnJobs (including havoc sanitizer crashes: the path may still have
  unexplored RSan bug edges). A focused sanitizer crash closes that RSan bug
  child as terminal instead of inserting.
*/

#include "dfsan/dfsan.h"

#include "sedbt.hpp"
#include "analyzer_client.hpp"

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

// Analyzer bootstrap InsertTrace is pipe-full. Steady-state LearnJobs use
// suffix capture inside symafl-analyzer, not this process.

#undef alloc_printf
#define alloc_printf(_str...) ({ \
    char* _tmp; \
    s32 _len = snprintf(NULL, 0, _str); \
    if (_len < 0) FATAL("Whoa, snprintf() fails?!"); \
    _tmp = (char*)ck_alloc(_len + 1); \
    snprintf((char*)_tmp, _len + 1, _str); \
    _tmp; \
  })

struct SeedLearn {
  uint8_t learned = symafl::kWalkFail;
  uint32_t frontier = sedbt::kUnexplored;
  uint8_t dir = 0;
  uint32_t skip_cnt = 0;
  uint32_t last_node = sedbt::kUnexplored;
  uint8_t last_dir = 0;
  uint32_t path_s_off = 0;
  uint16_t path_s_n = 0;
  uint16_t path_s_cons_n = 0;
  uint8_t path_s_ready = 0;
  uint8_t have_frontier = 0;  // 1 = LearnJob edge is this seed's suffix start
  std::vector<uint32_t> rsan_nodes;
};

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
    analyzer_close(&analyzer);
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

  sedbt::Tree tree{nullptr};
  std::unordered_set<std::string> traced_entries;
  bool bootstrap_done = false;

  // screening gates LearnJobs (bootstrap flush + gain-gated insert).
  // Concrete never skips: CheckInput is a learn-gate only (ADR 0009).
  bool screening = true;
  uint8_t rlimit = 16;
  uint8_t len_rlimit = 16;
  sedbt::NodeRef last_node = sedbt::kUnexplored;
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
  bool analyzer_mode = false;
  AnalyzerClient analyzer;
  std::unordered_map<std::string, SeedLearn> seed_learn;
  std::vector<uint32_t> current_open_rsan;
  uint32_t current_path_s_off = 0;
  uint16_t current_path_s_n = 0;
  uint16_t current_path_s_cons_n = 0;
  std::vector<u8> parent_seed;  // queue_get bytes; AFL havoc CONS_SAN compare
  uint32_t current_frontier = sedbt::kUnexplored;
  uint8_t current_dir = 0;
  uint8_t current_have_frontier = 0;
  uint8_t current_learned = symafl::kWalkFail;
  uint32_t explore_n = 0;
  uint32_t mut_i = 0;
  uint32_t explore_pct = 50;
  uint32_t havoc_pct = 25;   // SYMAFL_MUT_HAVOC_PCT; 0=no AFL havoc tail
  bool mut_path_s = true;    // SYMAFL_MUT_PATH_S != 0
  sedbt::PathSMode path_s_mode = sedbt::PathSMode::Suffix;
  bool mut_closure = true;   // SYMAFL_MUT_CLOSURE, default on
  bool path_s_screen = true; // SYMAFL_PATH_S_SCREEN: parent-suffix skip cov
  bool path_s_cons_san = true; // SYMAFL_PATH_S_CONS_SAN: GEP-index → fsrv_san
  symafl::SuffixScreenCache screen_cache;
  std::unordered_set<uint64_t> gep_skip_keys;  // one CONS_SAN skip per GEP value
  // Canonical MCE counters (docs/evaluation.md). Aliases below keep deinit
  // greps working: path_s_exec, path_s_san_exec, path_s_screened, …
  uint64_t fsrv_cov_exec = 0;
  uint64_t fsrv_cov_ns = 0;
  uint64_t fsrv_san_exec = 0;
  uint64_t fsrv_san_ns = 0;
  uint64_t cov_gain_cnt = 0;       // mutant fsrv_cov with new simplify_trace
  uint64_t con_san_cnt = 0;        // skip cov → fsrv_san (constraint symbol)
  uint64_t exp_tgt_mta_cnt = 0;    // path-s explore-targeting mutations
  uint64_t exp_tgt_mta_admit_cnt = 0;  // those that passed suffix screen
  uint64_t suffix_screen_ns = 0;   // time in suffix_vs_parent only
  uint64_t suffix_screen_steps = 0;  // nodes visited
  uint64_t suffix_screen_evals = 0;  // mutant eval_dir (parent dirs are cached)
  uint64_t fsrv_san_crash = 0;     // unique fsrv_san crashes (sig+pattern)
  uint64_t fsrv_cov_miss = 0;      // unique con_san crash, peek pattern seen
  uint64_t path_s_exec = 0;        // alias: admitted explore that ran fsrv_cov
  uint64_t path_s_san_exec = 0;    // alias: con_san_cnt
  uint64_t path_s_san_crash = 0;   // con_san crash events (not unique)
  uint64_t path_s_san_cov_miss = 0;  // alias: fsrv_cov_miss
  uint64_t path_s_screened = 0;    // alias: exp_tgt rejected by screen
  uint64_t closure_screened = 0;  // vuln: e_use fail after a same-length flip
  uint64_t closure_exec = 0;      // vuln mutant ran fsrv_san
  uint64_t default_exec = 0;      // AFL det/havoc (and other non-custom) concrete
  uint64_t vuln_ns = 0;           // mutate+screen + fsrv_san for vuln only
  std::unordered_set<uint32_t> seen_simplify;
  std::unordered_set<uint64_t> san_crash_keys;  // (sig<<32)|peek_hash
  bool last_cov_candidate = false;  // next fsrv_cov is a mutant (not cal)
  std::vector<u8> last_cov_buf;
  std::vector<u8> focused_scratch;
  uint32_t focused_rr = 0;
  uint64_t focused_rng = 1;
  bool focused_pending = false;  // e_use pass; post_process runs fsrv_san and skips concrete
  bool path_s_pending = false;   // path-s mutant; post_process admits concrete
  bool path_s_san_pending = false;  // constraint path-s; skip cov, fsrv_san
  uint32_t focused_rsan_node = ~0u;  // node used for the in-flight focused mutant
  std::unordered_set<uint32_t> closed_rsan;  // local: focused crash closed, SHM may lag
  // Pipeline accounting: concolic runs are executed only for coverage-gaining
  // admitted candidates (production) plus every admitted candidate under
  // REPLAY_ALL / probe_diag measurement modes.
  uint64_t concolic_run_calls = 0;
  uint64_t concolic_run_failed = 0;
  uint64_t san_run_calls = 0;        // alias: fsrv_san_exec
  uint64_t san_tmouts = 0;
  uint64_t san_crashes = 0;          // sanitizer crash events (all)
  uint64_t san_crashes_saved = 0;    // alias: fsrv_san_crash (unique files)
  uint64_t san_crash_seq = 0;        // monotonic id for saved crashes
  uint64_t learn_skip_san_crash = 0; // retained log field; havoc sanitizer crashes still learn
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

  // Historical veto-probe counters (always 0). Concrete never skips;
  // SYMAFL_VETO_PROBE_EVERY is rejected at init.
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
  sedbt::NodeRef probe_capture_node = sedbt::kUnexplored;
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
  sedbt::NodeRef last_veto_node = sedbt::kUnexplored;
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
  // edge -- with the identical SEDBT path. Both streams replayed through the
  // concolic target expose the decision the tree missed.
  FILE *pair_log = nullptr;
  char *pair_log_path = nullptr;
  // SYMAFL_PROBE_GAINED_LOG: append-only list of queue filenames that were
  // vetoed, probe-executed, and gained coverage. Used for end-of-run bitmap
  // checks: does the gain survive to the final bitmap, or was it superseded?
  FILE *probe_gained_log = nullptr;
  // SYMAFL_ADMITTED_GAINED_LOG records SEDBT admissions that created an AFL
  // queue entry. Together with the veto-probe log it permits exact terminal
  // bitmap accounting without treating seed or post-switch entries as SEDBT
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
// clock while profiling is disabled, and never alter SEDBT decisions,
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

// AFL++ measures exactly around afl_fsrv_run_target() on fsrv_cov.
extern "C" void afl_custom_exec_time(my_mutator_t *data,
                                      uint64_t elapsed_ns) {
  // Calibration + mutants. Peeks call afl_fsrv_run_target and skip this hook.
  data->fsrv_cov_exec += 1;
  data->fsrv_cov_ns += elapsed_ns;
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
  // symafl-analyzer (SYMAFL_ANALYZER_SOCK required). Optional sanitizer
  // forkserver is spawned by AFL++ after this init returns.
  const char *concolic = getenv("SYMAFL_CONCOLIC_TARGET");
  if (!concolic || !*concolic) {
    FATAL("SEDBT mode requires SYMAFL_CONCOLIC_TARGET (CLI target is the "
          "concrete binary)");
  }
  if (access(concolic, X_OK)) {
    PFATAL("SEDBT concolic target is not executable");
  }
  const char *san = getenv("SYMAFL_SANITIZER_TARGET");
  if (san && *san && access(san, X_OK)) {
    PFATAL("SEDBT sanitizer target is not executable");
  }
  data->afl->sedbt_mode = 1;
  data->concolic_target = (char *)ck_strdup((u8 *)concolic);
  if (san && *san) data->sanitizer_target = (char *)ck_strdup((u8 *)san);

  if (const char *mode = getenv("SYMAFL_TRACE_MODE")) {
    WARNF("SYMAFL_TRACE_MODE=%s is ignored: SEDBT transport is selected "
          "by lifecycle (bootstrap=pipe-full, steady=shm-suffix, "
          "overflow+gain=pipe-suffix)\n", mode);
  }
  if (getenv("SYMAFL_WORKER_SOCK") || getenv("SYMAFL_PCBT_DEBUG")) {
    FATAL("SYMAFL_WORKER_SOCK was renamed to SYMAFL_ANALYZER_SOCK; "
          "SYMAFL_PCBT_DEBUG was renamed to SYMAFL_SEDBT_DEBUG");
  }
  const char *wsock = getenv("SYMAFL_ANALYZER_SOCK");
  if (!wsock || !*wsock) {
    FATAL("SEDBT mode requires SYMAFL_ANALYZER_SOCK "
          "(concolic is symafl-analyzer; ADR 0010)");
  }
  data->analyzer_mode = true;
  if (!analyzer_connect(&data->analyzer, wsock)) {
    FATAL("SYMAFL_ANALYZER_SOCK connect failed: %s", wsock);
  }
  fprintf(stderr, "[sedbt] analyzer client connected (%s)\n", wsock);

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
    fprintf(stderr, "[sedbt] immediate forensics: %s (limit=%llu per reason)\n",
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
                "[sedbt] anomaly case dump: %s (entry/replay hard faults "
                "save probe+admit pair: input/pipe/events)\n",
                data->anomaly_case_dir);
      }
    }
  }

  if (getenv("SYMAFL_REPLAY_CHECK")) {
    data->replay_check = true;
    fprintf(stderr, "[sedbt] replay check enabled: all admitted candidates "
            "use full-pipe capture and trace replay validation\n");
  }
  if (getenv("SYMAFL_REPLAY_ALL")) {
    data->replay_all = true;
    data->replay_check = true;
    fprintf(stderr, "[sedbt] replay-all enabled: EVERY admitted run (gaining "
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
              "[sedbt] abort-on-residual: first hard residual sets stop_soon "
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
    fprintf(stderr, "[sedbt] rlimit unlimited (rCnt removed; unexplored "
            "always admits)\n");
  }
  if (const char *ep = getenv("SYMAFL_MUT_EXPLORE_PCT")) {
    long v = strtol(ep, nullptr, 10);
    if (v < 0) v = 0;
    if (v > 100) v = 100;
    data->explore_pct = (uint32_t)v;
    fprintf(stderr, "[sedbt] mutate explore_pct=%u (rest=vuln)\n",
            data->explore_pct);
  }
  if (const char *hp = getenv("SYMAFL_MUT_HAVOC_PCT")) {
    long v = strtol(hp, nullptr, 10);
    if (v < 0) v = 0;
    if (v > 100) v = 100;
    data->havoc_pct = (uint32_t)v;
  }
  {
    if (const char *e = getenv("SYMAFL_MUT_PATH_S")) {
      data->path_s_mode = sedbt::parse_mut_path_s_env(e);
      data->mut_path_s = data->path_s_mode != sedbt::PathSMode::Off;
    }
    if (const char *e = getenv("SYMAFL_MUT_CLOSURE"))
      data->mut_closure = strcmp(e, "0") != 0;
    if (const char *e = getenv("SYMAFL_PATH_S_SCREEN"))
      data->path_s_screen = strcmp(e, "0") != 0;
    if (const char *e = getenv("SYMAFL_PATH_S_CONS_SAN"))
      data->path_s_cons_san = strcmp(e, "0") != 0;
    data->tree.set_path_s_mode(data->path_s_mode);
    data->tree.set_compute_closures(data->mut_closure);
    fprintf(stderr, "[sedbt] mutate path_s=%s closure=%s havoc_pct=%u "
            "path_s_screen=%s path_s_cons_san=%s (0 disables that side / "
            "AFL havoc tail / parent-suffix skip / GEP-index→fsrv_san)\n",
            sedbt::path_s_mode_name(data->path_s_mode),
            data->mut_closure ? "on" : "off", data->havoc_pct,
            data->path_s_screen ? "on" : "off",
            data->path_s_cons_san ? "on" : "off");
  }
  if (getenv("SYMAFL_VETO") || getenv("SYMAFL_NO_VETO") ||
      getenv("SYMAFL_VETO_PROBE_EVERY")) {
    FATAL("SYMAFL_VETO / SYMAFL_NO_VETO / SYMAFL_VETO_PROBE_EVERY are removed. "
          "Concrete always admits; CheckInput is a learn-gate (ADR 0009)");
  }
  fprintf(stderr,
          "[sedbt] CheckInput is a learn-gate (ADR 0009). "
          "Path-s parent-suffix screen may skip concrete "
          "(SYMAFL_PATH_S_SCREEN); tainted GEP-index mutants "
          "skip cov once per GEP value and run fsrv_san "
          "(SYMAFL_PATH_S_CONS_SAN); havoc never skips.\n");
  if (getenv("SYMAFL_NO_SCREEN")) {
    data->screening = false;
    fprintf(stderr, "[sedbt] SYMAFL_NO_SCREEN: no LearnJobs, no concolic insert\n");
  }
  if (const char *root_shm = getenv("SYMAFL_ROOT_SHM")) {
    data->root_shm_enabled = strcmp(root_shm, "0") != 0;
    fprintf(stderr, "[sedbt] root SHM capture %s (SYMAFL_ROOT_SHM=%s)\n",
            data->root_shm_enabled ? "enabled" : "disabled", root_shm);
  }
  if (getenv("SYMAFL_PROFILE")) {
    data->profile_enabled = true;
    data->tree.set_profile(true);
    fprintf(stderr, "[sedbt] profiling enabled (SYMAFL_PROFILE=1)\n");
  }
  if (getenv("SYMAFL_SEDBT_DEBUG")) {
    data->tree.set_debug(true);
    fprintf(stderr, "[sedbt] predicate debug enabled (SYMAFL_SEDBT_DEBUG=1)\n");
  }
  if (getenv("SYMAFL_CONFLICT_DIAG")) {
    data->tree.set_conflict_diag(true);
    fprintf(stderr, "[sedbt] conflict-site diagnostics enabled "
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
  fprintf(stderr, "[sedbt] retry limits: base=%u len_constraint=%u\n",
          (unsigned)data->rlimit, (unsigned)data->len_rlimit);
  // Probe-case persistence for replay-all forensics.
  if (data->replay_all) {
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
    fprintf(stderr, "[sedbt] probe cases: %s (queue/bitmap isolated)\n",
            data->probe_case_dir);
  }
  if (getenv("SYMAFL_PROBE_DIAG")) {
    data->probe_diag = true;
    fprintf(stderr, "[sedbt] probe diagnostic enabled (SYMAFL_PROBE_DIAG=1)\n");
  }
  if (getenv("SYMAFL_PROBE_LEARN")) {
    data->probe_learn = true;
    fprintf(stderr, "[sedbt] probe learn enabled (SYMAFL_PROBE_LEARN=1): "
                    "a coverage-gaining rlimit probe inserts its suffix and "
                    "refreshes the frontier edge's retry budget\n");
  }
  if (const char *pl = getenv("SYMAFL_PAIR_LOG")) {
    data->pair_log_path = (char *)ck_strdup((u8 *)pl);
    data->pair_log = fopen(pl, "w");
    if (!data->pair_log) {
      FATAL("cannot open SYMAFL_PAIR_LOG=%s", pl);
    }
    fprintf(stderr, "[sedbt] pair forensics log: %s\n", pl);
  }
  if (const char *pgl = getenv("SYMAFL_PROBE_GAINED_LOG")) {
    data->probe_gained_log = fopen(pgl, "w");
    if (!data->probe_gained_log) {
      FATAL("cannot open SYMAFL_PROBE_GAINED_LOG=%s", pgl);
    }
    fprintf(stderr, "[sedbt] probe-gained log: %s\n", pgl);
  }
  if (const char *agl = getenv("SYMAFL_ADMITTED_GAINED_LOG")) {
    data->admitted_gained_log = fopen(agl, "w");
    if (!data->admitted_gained_log) {
      FATAL("cannot open SYMAFL_ADMITTED_GAINED_LOG=%s", agl);
    }
    fprintf(stderr, "[sedbt] admitted-gained log: %s\n", agl);
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
    fprintf(stderr, "[sedbt] progress log: %s (interval=%llums)\n", progress,
            (unsigned long long)data->progress_interval_ms);
  }
  if (const char *cd = getenv("SYMAFL_CONCOLIC_SECONDS")) {
    char *end = nullptr;
    unsigned long long parsed = strtoull(cd, &end, 10);
    if (end == cd || *end != '\0' || parsed == 0) {
      FATAL("Invalid SYMAFL_CONCOLIC_SECONDS=%s", cd);
    }
    data->concolic_deadline = parsed;
    fprintf(stderr, "[sedbt] concolic phase deadline: %llus\n",
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
    fprintf(stderr, "[sedbt] probe-gain saturation window enabled: "
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
  data->mut_i = 0;
  data->explore_n = 0;
  if (data->current_learned != symafl::kReady) return 0;
  const bool have_explore = data->mut_path_s && data->current_path_s_n > 0;
  const bool have_vuln = data->mut_closure && !data->current_open_rsan.empty();
  if (!have_explore && !have_vuln) return 0;
  u32 ps = 100;
  u32 hd = 1;
  if (data->afl) {
    if (data->afl->queue_cur && data->afl->queue_cur->perf_score > 1.0)
      ps = (u32)data->afl->queue_cur->perf_score;
    if (ps > 0xffff) ps = 0xffff;
    if (data->afl->havoc_div) hd = data->afl->havoc_div;
  }
  u32 energy = (HAVOC_CYCLES * ps / hd) >> 8;
  if (energy < HAVOC_MIN) energy = HAVOC_MIN;
  if (energy > 4096) energy = 4096;
  if (!have_vuln) {
    data->explore_n = energy;
    return energy;
  }
  if (!have_explore) {
    data->explore_n = 0;
    return energy;
  }
  data->explore_n = energy * data->explore_pct / 100;
  if (data->explore_pct > 0 && data->explore_n == 0) data->explore_n = 1;
  if (data->explore_pct < 100 && data->explore_n >= energy)
    data->explore_n = energy - 1;
  return energy;
}

static uint32_t focused_rand(my_mutator_t *data, uint32_t limit) {
  if (limit <= 1) return 0;
  data->focused_rng = data->focused_rng * 6364136223846793005ULL + 1;
  return (uint32_t)(data->focused_rng >> 33) % limit;
}

static bool s_has(const uint32_t *offs, uint16_t n, uint32_t off) {
  for (uint16_t i = 0; i < n; ++i)
    if (offs[i] == off) return true;
  return false;
}

// Same-length stacked havoc restricted to offsets in S. Returns false if
// no in-range symbol (caller should fall through, not count screened).
static bool s_havoc(my_mutator_t *data, u8 *buf, size_t len,
                    const uint32_t *offs, uint16_t n) {
  if (!buf || !len || !offs || !n) return false;
  bool any = false;
  for (uint16_t i = 0; i < n; ++i)
    if (offs[i] < len) {
      any = true;
      break;
    }
  if (!any) return false;
  static const int8_t kI8[] = {-128, -1, 0, 1, 16, 32, 64, 100, 127};
  static const int16_t kI16[] = {-32768, -129, 128, 255, 256, 512, 1000, 1024,
                                 4096, 32767};
  static const int32_t kI32[] = {
      (int32_t)0x80000000, -100663046, -32769, 32768, 65535, 65536, 100663045,
      2139095040, 2147483647};
  const uint32_t stack = 1u << focused_rand(data, 4);
  for (uint32_t s = 0; s < stack; ++s) {
    uint32_t off = offs[focused_rand(data, n)];
    if (off >= len) continue;
    const bool w2 = (off + 1 < len) && s_has(offs, n, off + 1);
    const bool w4 =
        w2 && (off + 3 < len) && s_has(offs, n, off + 2) && s_has(offs, n, off + 3);
    uint32_t nops = 4 + (w2 ? 2 : 0) + (w4 ? 2 : 0);
    uint32_t op = focused_rand(data, nops);
    if (op == 0) {
      buf[off] = (u8)focused_rand(data, 256);
    } else if (op == 1) {
      buf[off] ^= (u8)(1u << focused_rand(data, 8));
    } else if (op == 2) {
      uint32_t d = 1 + focused_rand(data, 35);
      buf[off] = focused_rand(data, 2) ? (u8)(buf[off] + d) : (u8)(buf[off] - d);
    } else if (op == 3) {
      buf[off] = (u8)kI8[focused_rand(data, (uint32_t)sizeof(kI8))];
    } else if (w2 && (op == 4 || op == 5)) {
      uint16_t cur = (uint16_t)buf[off] | ((uint16_t)buf[off + 1] << 8);
      uint16_t nxt;
      if (op == 4) {
        nxt = (uint16_t)kI16[focused_rand(data, (uint32_t)(sizeof(kI16) / 2))];
      } else {
        uint32_t d = 1 + focused_rand(data, 35);
        nxt = focused_rand(data, 2) ? (uint16_t)(cur + d) : (uint16_t)(cur - d);
      }
      buf[off] = (u8)nxt;
      buf[off + 1] = (u8)(nxt >> 8);
    } else if (w4) {
      uint32_t cur = (uint32_t)buf[off] | ((uint32_t)buf[off + 1] << 8) |
                     ((uint32_t)buf[off + 2] << 16) |
                     ((uint32_t)buf[off + 3] << 24);
      uint32_t nxt;
      if (op == nops - 2) {
        nxt = (uint32_t)kI32[focused_rand(data, (uint32_t)(sizeof(kI32) / 4))];
      } else {
        uint32_t d = 1 + focused_rand(data, 35);
        nxt = focused_rand(data, 2) ? cur + d : cur - d;
      }
      buf[off] = (u8)nxt;
      buf[off + 1] = (u8)(nxt >> 8);
      buf[off + 2] = (u8)(nxt >> 16);
      buf[off + 3] = (u8)(nxt >> 24);
    }
  }
  return true;
}

static const symafl::ShmClosure *shm_clos(const symafl::SedbtShm *shm,
                                         const symafl::ShmNode &n) {
  if (!shm || !n.clos_i) return nullptr;
  uint32_t i = n.clos_i - 1;
  uint32_t nc = shm->hdr.n_clos.load(std::memory_order_acquire);
  if (i >= nc || i >= shm->hdr.clos_cap) return nullptr;
  return &shm->clos[i];
}

static bool load_shm_closure(const symafl::SedbtShm *shm, uint32_t ref,
                             sedbt::AttachedClosure *out) {
  if (!shm || !out || ref < sedbt::kRoot) return false;
  uint32_t nn = shm->hdr.n_nodes.load(std::memory_order_acquire);
  if (ref >= nn) return false;
  const symafl::ShmNode &n = shm->nodes[ref];
  const symafl::ShmClosure *c = shm_clos(shm, n);
  if (!c || n.rsan_bug_dir > 1) return false;
  out->node = ref;
  out->bug_dir = n.rsan_bug_dir;
  out->trigger_neg = c->trigger_neg;
  out->trigger_root = n.pred_root;
  out->s.assign(shm->s_offs + c->s_off, shm->s_offs + c->s_off + c->s_n);
  out->e.clear();
  out->e.reserve(c->e_n);
  for (uint16_t i = 0; i < c->e_n; ++i) {
    const symafl::ShmClause &cl = shm->e_clauses[c->e_off + i];
    out->e.push_back({cl.pred_root, cl.negated});
  }
  return !out->s.empty();
}

static bool rsan_bug_open(const symafl::SedbtShm *shm, uint32_t ref) {
  if (!shm || ref < sedbt::kRoot) return false;
  uint32_t nn = shm->hdr.n_nodes.load(std::memory_order_acquire);
  if (ref >= nn) return false;
  const symafl::ShmNode &n = shm->nodes[ref];
  if (n.rsan_bug_dir > 1 || !n.clos_i) return false;
  uint32_t bug = __atomic_load_n(&shm->nodes[ref].child[n.rsan_bug_dir],
                                 __ATOMIC_ACQUIRE);
  return bug == sedbt::kUnexplored;
}

static bool rsan_bug_open(my_mutator_t *data, uint32_t ref) {
  if (!data || data->closed_rsan.count(ref)) return false;
  return rsan_bug_open(data->analyzer.tree, ref);
}

static bool eval_focused(my_mutator_t *data, const sedbt::AttachedClosure &c,
                         const u8 *buf, uint32_t len) {
  if (data->analyzer_mode && data->analyzer.tree) {
    uint32_t np =
        data->analyzer.tree->hdr.n_preds.load(std::memory_order_acquire);
    return sedbt::eval_e_use(data->analyzer.tree->preds, np, c, buf, len);
  }
  return data->tree.eval_attached(c, buf, len);
}

static bool cons_offsets_changed(my_mutator_t *data, const u8 *parent,
                                 size_t plen, const u8 *mut, size_t mlen) {
  if (!data->path_s_cons_san || !data->current_path_s_cons_n) return false;
  if (!parent || !plen || !mut || !data->analyzer.tree) return false;
  uint32_t n_s = data->analyzer.tree->hdr.n_s.load(std::memory_order_acquire);
  if (data->current_path_s_off + data->current_path_s_cons_n > n_s)
    return false;
  const uint32_t *offs =
      data->analyzer.tree->s_offs + data->current_path_s_off;
  for (uint16_t i = 0; i < data->current_path_s_cons_n; ++i) {
    uint32_t o = offs[i];
    if (o >= plen) continue;
    if (o >= mlen || parent[o] != mut[o]) return true;
  }
  return false;
}

static uint64_t gep_value_key(my_mutator_t *data, const u8 *buf, size_t len) {
  uint64_t h = 14695981039346656037ull;
  const uint32_t *offs =
      data->analyzer.tree->s_offs + data->current_path_s_off;
  for (uint16_t i = 0; i < data->current_path_s_cons_n; ++i) {
    uint32_t o = offs[i];
    uint8_t b = (o < len) ? buf[o] : 0xff;
    h ^= b;
    h *= 1099511628211ull;
    h ^= (uint64_t)(o + 1) * 0x9e3779b97f4a7c15ull;
    h *= 1099511628211ull;
  }
  return h;
}

// Skip fsrv_cov only for a new GEP-index byte tuple. Repeat values, and
// indcall/read-length pins (not in term_cons_n), run coverage.
static bool cons_san_should_skip(my_mutator_t *data, const u8 *parent,
                                 size_t plen, const u8 *mut, size_t mlen) {
  if (!cons_offsets_changed(data, parent, plen, mut, mlen)) return false;
  const uint64_t key = gep_value_key(data, mut, mlen);
  return data->gep_skip_keys.insert(key).second;
}

enum SanFrom { kSanCovGain = 1, kSanConSan = 2, kSanFocused = 3 };

static uint32_t bits_hash32(const u8 *key, u32 len) {
  uint32_t h = 2166136261u;
  for (u32 i = 0; i < len; ++i) {
    h ^= key[i];
    h *= 16777619u;
  }
  return h;
}

static uint32_t simplify_hash_bits(const u8 *bits, u32 map_size) {
  if (!bits || map_size < 8) return 0;
  const u32 n = map_size & ~7u;
  std::vector<u8> tmp(n);
  memcpy(tmp.data(), bits, n);
  u64 *mem = (u64 *)tmp.data();
  u32 words = n >> 3;
  while (words--) {
    if (*mem) {
      u8 *m8 = (u8 *)mem;
      for (int k = 0; k < 8; k++) m8[k] = m8[k] ? 128 : 1;
    } else {
      *mem = 0x0101010101010101ULL;
    }
    mem++;
  }
  return bits_hash32(tmp.data(), n);
}

static uint32_t peek_cov_simplify(my_mutator_t *data, const u8 *buf, size_t len,
                                  bool *out_cov_crash) {
  if (out_cov_crash) *out_cov_crash = false;
  afl_forkserver_t *fsrv = &data->afl->fsrv;
  if (fsrv->fsrv_pid <= 0 || !buf || len == 0) return 0;
  afl_fsrv_write_to_testcase(fsrv, const_cast<u8 *>(buf), len);
  fsrv_run_result_t r =
      afl_fsrv_run_target(fsrv, fsrv->exec_tmout, &data->afl->stop_soon);
  if (r == FSRV_RUN_CRASH) {
    if (out_cov_crash) *out_cov_crash = true;
    return 0;
  }
  u32 n = fsrv->real_map_size ? fsrv->real_map_size : fsrv->map_size;
  if (n > fsrv->map_size) n = fsrv->map_size;
  return simplify_hash_bits(fsrv->trace_bits, n);
}

static bool run_sanitizer_on(my_mutator_t *data, const u8 *buf, size_t len,
                             SanFrom from);

static void mark_cov_candidate(my_mutator_t *data, const u8 *buf, size_t len) {
  data->last_cov_candidate = true;
  data->last_cov_buf.assign(buf, buf + len);
}

extern "C" size_t afl_custom_fuzz(my_mutator_t *data, u8 *buf, size_t buf_size,
                                  u8 **out_buf, u8 *add_buf,
                                  size_t add_buf_size, size_t max_size) {
  (void)add_buf;
  (void)add_buf_size;
  (void)max_size;
  data->focused_pending = false;
  data->path_s_pending = false;
  data->path_s_san_pending = false;
  data->focused_rsan_node = ~0u;
  if (buf_size == 0) {
    *out_buf = buf;
    return 0;
  }
  if (data->focused_scratch.size() < buf_size)
    data->focused_scratch.resize(buf_size);
  memcpy(data->focused_scratch.data(), buf, buf_size);

  const bool do_explore = data->mut_i < data->explore_n;
  data->mut_i += 1;

  if (!do_explore && data->mut_closure && data->analyzer.tree) {
    auto drop_open = [&](uint32_t ref) {
      auto &open = data->current_open_rsan;
      open.erase(std::remove(open.begin(), open.end(), ref), open.end());
    };
    while (!data->current_open_rsan.empty()) {
      uint32_t ref = data->current_open_rsan[data->focused_rr++ %
                                            data->current_open_rsan.size()];
      if (!rsan_bug_open(data, ref)) {
        drop_open(ref);
        continue;
      }
      sedbt::AttachedClosure c;
      if (!load_shm_closure(data->analyzer.tree, ref, &c)) {
        drop_open(ref);
        continue;
      }
      uint16_t sn = c.s.size() > 0xffff ? 0xffff : (uint16_t)c.s.size();
      const uint64_t t0 = profile_now();
      if (!s_havoc(data, data->focused_scratch.data(), buf_size, c.s.data(),
                   sn)) {
        break;
      }
      if (!eval_focused(data, c, data->focused_scratch.data(),
                        (uint32_t)buf_size)) {
        data->closure_screened += 1;
        data->vuln_ns += profile_now() - t0;
        *out_buf = data->focused_scratch.data();
        return 0;
      }
      data->closure_exec += 1;
      data->focused_pending = true;
      data->focused_rsan_node = ref;
      data->vuln_ns += profile_now() - t0;
      *out_buf = data->focused_scratch.data();
      return buf_size;
    }
  }

  if (data->mut_path_s && data->current_path_s_n && data->analyzer.tree) {
    uint32_t n_s = data->analyzer.tree->hdr.n_s.load(std::memory_order_acquire);
    const uint32_t *offs =
        data->analyzer.tree->s_offs + data->current_path_s_off;
    if (data->current_path_s_off + data->current_path_s_n <= n_s &&
        s_havoc(data, data->focused_scratch.data(), buf_size, offs,
                data->current_path_s_n)) {
      data->exp_tgt_mta_cnt += 1;
      if (data->path_s_screen && data->current_have_frontier) {
        uint32_t sc_front = data->current_frontier;
        uint8_t sc_dir = data->current_dir;
        if (data->path_s_mode == sedbt::PathSMode::Full) {
          sc_front = sedbt::kRoot;
          sc_dir = 0;
        }
        const uint64_t tscr = profile_now();
        symafl::SuffixWalkStats st{};
        symafl::SuffixCmp cmp;
        if (data->screen_cache.dir <= 1 &&
            data->screen_cache.frontier == sc_front &&
            data->screen_cache.dir == sc_dir) {
          cmp = symafl::suffix_vs_parent_cached(
              data->analyzer.tree, &data->screen_cache,
              data->focused_scratch.data(), (uint32_t)buf_size, &st);
        } else {
          cmp = symafl::suffix_vs_parent(
              data->analyzer.tree, sc_front, sc_dir, buf, (uint32_t)buf_size,
              data->focused_scratch.data(), (uint32_t)buf_size);
        }
        data->suffix_screen_ns += profile_now() - tscr;
        data->suffix_screen_steps += st.steps;
        data->suffix_screen_evals += st.evals;
        if (cmp == symafl::SuffixCmp::Same ||
            cmp == symafl::SuffixCmp::Explored) {
          data->path_s_screened += 1;
          *out_buf = data->focused_scratch.data();
          return 0;
        }
      }
      data->exp_tgt_mta_admit_cnt += 1;
      if (cons_san_should_skip(data, buf, buf_size,
                               data->focused_scratch.data(), buf_size) &&
          data->afl->fsrv_san.fsrv_pid > 0) {
        data->path_s_san_pending = true;
        *out_buf = data->focused_scratch.data();
        return buf_size;
      }
      data->path_s_exec += 1;
      data->path_s_pending = true;
      *out_buf = data->focused_scratch.data();
      return buf_size;
    }
  }
  *out_buf = buf;
  return 0;
}

extern "C" void afl_custom_deinit(my_mutator_t *data) {
  write_progress(data, true);
  const sedbt::Tree &t = data->tree;
  fprintf(stderr,
          "[sedbt] traces=%llu nodes=%llu pred_nodes=%llu depth=%llu conflicts=%llu "
          "opaque=%llu tautology=%llu struct_err=%llu struct_convert=%llu struct_train=%llu failed=%llu timeouts=%llu memerr=%llu screened=%llu "
          "admitted=%llu vetoed=%llu traced_entries=%llu saturated=%llu "
          "single_pass=%llu single_pass_overflow=%llu "
          "admit_empty=%llu admit_opaque=%llu follow_tautology=%llu admit_eval_failure=%llu admit_frontier=%llu admit_unstable=%llu "
          "admit_len_veto=%llu veto_terminal=%llu veto_rlimit=%llu veto_unstable=%llu probe_admitted=%llu probe_gained=%llu "
          "probe_gained_terminal=%llu probe_gained_rlimit=%llu profile=%d "
          "concolic_runs=%llu concolic_failed=%llu "
          "san_runs=%llu san_tmouts=%llu san_crashes=%llu san_saved=%llu "
          "learn_skip_san=%llu "
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
          (unsigned long long)data->learn_skip_san_crash,
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
  if (data->analyzer.tree) {
    fprintf(stderr, "[sedbt] analyzer_shm nodes=%u preds=%u\n",
            data->analyzer.tree->hdr.n_nodes.load(std::memory_order_acquire),
            data->analyzer.tree->hdr.n_preds.load(std::memory_order_acquire));
  }
  {
    const uint64_t vuln_att =
        data->closure_screened + data->closure_exec;
    const double vuln_rate =
        data->vuln_ns ? (double)vuln_att * 1e9 / (double)data->vuln_ns : 0.0;
    fprintf(stderr,
            "[sedbt] path_s_exec=%llu path_s_san_exec=%llu "
            "path_s_san_crash=%llu path_s_san_cov_miss=%llu "
            "path_s_screened=%llu "
            "closure_screened=%llu closure_exec=%llu "
            "exec=%llu vuln_ns=%llu vuln_rate=%.2f/s "
            "mut_path_s=%s mut_closure=%u path_s_screen=%u "
            "path_s_cons_san=%u closure_seeds=%llu\n",
            (unsigned long long)data->path_s_exec,
            (unsigned long long)data->path_s_san_exec,
            (unsigned long long)data->path_s_san_crash,
            (unsigned long long)data->path_s_san_cov_miss,
            (unsigned long long)data->path_s_screened,
            (unsigned long long)data->closure_screened,
            (unsigned long long)data->closure_exec,
            (unsigned long long)data->default_exec,
            (unsigned long long)data->vuln_ns, vuln_rate,
            sedbt::path_s_mode_name(data->path_s_mode),
            (unsigned)data->mut_closure,
            (unsigned)data->path_s_screen,
            (unsigned)data->path_s_cons_san,
            (unsigned long long)data->seed_learn.size());
    const double cov_tp = data->fsrv_cov_ns
        ? (double)data->fsrv_cov_exec * 1e9 / (double)data->fsrv_cov_ns : 0.0;
    const double san_tp = data->fsrv_san_ns
        ? (double)data->fsrv_san_exec * 1e9 / (double)data->fsrv_san_ns : 0.0;
    const double scr_tp = data->suffix_screen_ns
        ? (double)data->exp_tgt_mta_cnt * 1e9 / (double)data->suffix_screen_ns
        : 0.0;
    const uint64_t cov_crash =
        data->afl ? (uint64_t)data->afl->saved_crashes : 0;
    const uint64_t queue_n =
        data->afl ? (uint64_t)data->afl->queued_items : 0;
    fprintf(stderr,
            "[sedbt-mce] fsrv_cov_exec=%llu fsrv_cov_ns=%llu "
            "fsrv_cov_throughput=%.2f "
            "fsrv_san_exec=%llu fsrv_san_ns=%llu fsrv_san_throughput=%.2f "
            "cov_gain_cnt=%llu con_san_cnt=%llu "
            "exp_tgt_mta_cnt=%llu exp_tgt_mta_admit_cnt=%llu "
            "suffix_screen_ns=%llu suffix_screen_throughput=%.2f "
            "suffix_screen_steps=%llu suffix_screen_evals=%llu "
            "fsrv_san_crash=%llu fsrv_cov_crash=%llu fsrv_cov_miss=%llu "
            "queue_seed_cnt=%llu "
            "closure_exec=%llu fsrv_san_identity=%llu\n",
            (unsigned long long)data->fsrv_cov_exec,
            (unsigned long long)data->fsrv_cov_ns, cov_tp,
            (unsigned long long)data->fsrv_san_exec,
            (unsigned long long)data->fsrv_san_ns, san_tp,
            (unsigned long long)data->cov_gain_cnt,
            (unsigned long long)data->con_san_cnt,
            (unsigned long long)data->exp_tgt_mta_cnt,
            (unsigned long long)data->exp_tgt_mta_admit_cnt,
            (unsigned long long)data->suffix_screen_ns, scr_tp,
            (unsigned long long)data->suffix_screen_steps,
            (unsigned long long)data->suffix_screen_evals,
            (unsigned long long)data->fsrv_san_crash,
            (unsigned long long)cov_crash,
            (unsigned long long)data->fsrv_cov_miss,
            (unsigned long long)queue_n,
            (unsigned long long)data->closure_exec,
            (unsigned long long)(data->cov_gain_cnt + data->con_san_cnt +
                                 data->closure_exec));
    if (data->afl && data->afl->out_dir) {
      char *mp = alloc_printf("%s/mce_stats.txt", data->afl->out_dir);
      FILE *mf = fopen(mp, "w");
      if (mf) {
        fprintf(mf,
                "fsrv_cov_exec=%llu\nfsrv_cov_ns=%llu\nfsrv_cov_throughput=%.6f\n"
                "fsrv_san_exec=%llu\nfsrv_san_ns=%llu\nfsrv_san_throughput=%.6f\n"
                "cov_gain_cnt=%llu\ncon_san_cnt=%llu\n"
                "exp_tgt_mta_cnt=%llu\nexp_tgt_mta_admit_cnt=%llu\n"
                "suffix_screen_ns=%llu\nsuffix_screen_throughput=%.6f\n"
                "suffix_screen_steps=%llu\nsuffix_screen_evals=%llu\n"
                "fsrv_san_crash=%llu\nfsrv_cov_crash=%llu\nfsrv_cov_miss=%llu\n"
                "queue_seed_cnt=%llu\n"
                "closure_exec=%llu\n"
                "fsrv_san_identity=%llu\n"
                "bitmap_cvg_note=see fuzzer_stats\n"
                "seed_exe_depth_note=post-campaign measure-seed-exe-depth.py\n",
                (unsigned long long)data->fsrv_cov_exec,
                (unsigned long long)data->fsrv_cov_ns, cov_tp,
                (unsigned long long)data->fsrv_san_exec,
                (unsigned long long)data->fsrv_san_ns, san_tp,
                (unsigned long long)data->cov_gain_cnt,
                (unsigned long long)data->con_san_cnt,
                (unsigned long long)data->exp_tgt_mta_cnt,
                (unsigned long long)data->exp_tgt_mta_admit_cnt,
                (unsigned long long)data->suffix_screen_ns, scr_tp,
                (unsigned long long)data->suffix_screen_steps,
                (unsigned long long)data->suffix_screen_evals,
                (unsigned long long)data->fsrv_san_crash,
                (unsigned long long)cov_crash,
                (unsigned long long)data->fsrv_cov_miss,
                (unsigned long long)queue_n,
                (unsigned long long)data->closure_exec,
                (unsigned long long)(data->cov_gain_cnt + data->con_san_cnt +
                                     data->closure_exec));
        fclose(mf);
      }
      ck_free(mp);
    }
  }
  if (data->forensics_dir || data->anomaly_case_dir) {
    fprintf(stderr,
            "[sedbt-forensics] dir=%s anomaly_dir=%s opaque_seen=%llu "
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
            "[sedbt-struct] total=%llu convert_fail=%llu train_mismatch=%llu\n",
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
        fprintf(stderr, "[sedbt-struct-cid] cid=%u count=%llu\n",
                ranked[i].first, (unsigned long long)ranked[i].second);
      }
    }
  }
  if (data->profile_enabled) {
    const uint64_t calls = data->profile_check_calls;
    fprintf(stderr,
            "[sedbt-profile] checks=%llu walk_nodes=%llu predicate_calls=%llu "
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
          "[sedbt-replay] checked=%llu cid_mismatch=%llu dir_mismatch=%llu "
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
          "[sedbt-opaque] invalid_root=%llu invalid_label=%llu initializing_label=%llu "
          "invalid_width=%llu depth_limit=%llu bad_load=%llu bad_concat=%llu "
          "unsupported_op=%llu unsupported_compare=%llu uncaptured_memcmp_operand=%llu "
          "arena_limit=%llu node_limit=%llu\n",
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::InvalidRoot],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::InvalidLabel],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::InitializingLabel],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::InvalidWidth],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::DepthLimit],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::BadLoad],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::BadConcat],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::UnsupportedOp],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::UnsupportedCompare],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::UncapturedMemcmpOperand],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::ArenaLimit],
          (unsigned long long)t.opaque_by_error[(size_t)sedbt::PredError::NodeLimit]);
  for (const auto &entry : t.opaque_by_op) {
    fprintf(stderr, "[sedbt-opaque-op] op=%u count=%llu\n", entry.first,
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
      fprintf(stderr, "[sedbt-opaque-cid] cid=%u count=%llu\n",
              by_cid[i].first, (unsigned long long)by_cid[i].second);
    }
  }
  // Tree topology dump for offline pair/terminal forensics
  // (SYMAFL_TREE_DUMP=<path>). The writable tree lives in the analyzer;
  // dump the live SHM view. Analyzer deinit may overwrite the same path.
  if (const char *dump = getenv("SYMAFL_TREE_DUMP")) {
    if (data->analyzer.tree) {
      symafl::dump_shm_tree(data->analyzer.tree, dump);
      fprintf(stderr, "[sedbt] analyzer shm dump -> %s nodes=%u\n", dump,
              data->analyzer.tree->hdr.n_nodes.load(std::memory_order_acquire));
    } else {
      data->tree.Dump(dump);
      fprintf(stderr, "[sedbt] tree dump -> %s\n", dump);
    }
  }
  // Step-by-step CheckInput evaluation of one candidate
  // (SYMAFL_EVAL_INPUT=<file>): prints every visited node (cid/skip/depth)
  // and the evaluated direction, to see where a candidate should have
  // forked from the tree path but did not.
  if (const char *eval = getenv("SYMAFL_EVAL_INPUT")) {
    FILE *f = fopen(eval, "rb");
    if (!f) {
      fprintf(stderr, "[sedbt] cannot open SYMAFL_EVAL_INPUT=%s\n", eval);
    } else {
      std::vector<u8> buf;
      uint8_t chunk[65536];
      size_t n;
      while ((n = fread(chunk, 1, sizeof(chunk), f)) > 0) {
        buf.insert(buf.end(), chunk, chunk + n);
      }
      fclose(f);
      data->tree.set_debug(true);
      sedbt::NodeRef node = sedbt::kUnexplored;
      uint8_t dir = 0;
      uint32_t vdepth = 0;
      sedbt::NodeRef vnode = sedbt::kUnexplored;
      uint8_t vdir = 0, vkind = 0;
      bool adm = data->tree.CheckInput(buf.data(), (uint32_t)buf.size(),
                                       &node, &dir, data->rlimit, &vdepth,
                                       &vnode, &vdir, &vkind,
                                       data->len_rlimit);
      fprintf(stderr,
              "[sedbt-eval] %s admitted=%d node=%u dir=%u veto_node=%u "
              "veto_dir=%u veto_depth=%u veto_kind=%u\n",
              eval, adm ? 1 : 0, node, dir, vnode, vdir, vdepth, vkind);
      data->tree.set_debug(false);
    }
  }
  if (data->probe_diag) {
    fprintf(stderr,
            "[sedbt-diag] probe_suffix_empty=%llu probe_suffix_nonempty=%llu "
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

static void close_focused_bug(my_mutator_t *data, uint32_t ref) {
  if (ref == ~0u || !data->analyzer.tree) return;
  uint32_t nn = data->analyzer.tree->hdr.n_nodes.load(std::memory_order_acquire);
  if (ref >= nn) return;
  uint8_t dir = data->analyzer.tree->nodes[ref].rsan_bug_dir;
  if (dir > 1) return;
  data->closed_rsan.insert(ref);
  auto &open = data->current_open_rsan;
  open.erase(std::remove(open.begin(), open.end(), ref), open.end());
  if (!analyzer_close_bug_edge(&data->analyzer, ref, dir)) {
    fprintf(stderr, "[sedbt] close-bug send failed node=%u dir=%u\n", ref, dir);
  } else {
    fprintf(stderr, "[sedbt] close-bug node=%u dir=%u\n", ref, dir);
  }
}

static void merge_rsan(SeedLearn *st, const std::vector<uint32_t> &add) {
  for (uint32_t n : add) {
    if (std::find(st->rsan_nodes.begin(), st->rsan_nodes.end(), n) ==
        st->rsan_nodes.end())
      st->rsan_nodes.push_back(n);
  }
}

static void take_terminal(SeedLearn *st, const symafl::WalkResult &wr) {
  st->learned = symafl::kReady;
  st->last_node = wr.last_node;
  st->last_dir = wr.last_dir;
  st->path_s_off = wr.path_s_off;
  st->path_s_n = wr.path_s_n;
  st->path_s_cons_n = wr.path_s_cons_n;
  st->path_s_ready = wr.path_s_ready;
  // Path-s was bound at the insert (retargeted) frontier, which may be
  // deeper than the LearnJob the fuzzer submitted. Adopt that bind site
  // so the next queue_get screens from the same edge.
  if (wr.frontier >= sedbt::kRoot && wr.dir <= 1) {
    st->frontier = wr.frontier;
    st->dir = wr.dir;
    st->have_frontier = 1;
  }
  merge_rsan(st, wr.rsan_nodes);
}

static bool try_submit_learn(my_mutator_t *data, SeedLearn *st, const u8 *buf,
                             uint32_t len) {
  if (analyzer_submit(&data->analyzer, st->frontier, st->dir, st->skip_cnt, buf,
                    len)) {
    st->learned = symafl::kInFlight;
    return true;
  }
  st->learned = symafl::kRingFull;
  return false;
}

static void collect_open(my_mutator_t *data, const SeedLearn &st,
                         const char *fname) {
  data->current_open_rsan.clear();
  data->current_path_s_off = 0;
  data->current_path_s_n = 0;
  data->current_path_s_cons_n = 0;
  data->current_frontier = st.frontier;
  data->current_dir = st.dir;
  data->current_have_frontier = st.have_frontier;
  data->current_path_s_off = st.path_s_off;
  data->current_path_s_cons_n = st.path_s_cons_n;
  if (data->mut_path_s) {
    data->current_path_s_n = st.path_s_n;
  }
  auto *shm = data->analyzer.tree;
  if (!shm || !data->mut_closure) return;
  for (uint32_t ref : st.rsan_nodes) {
    if (rsan_bug_open(data, ref)) data->current_open_rsan.push_back(ref);
  }
  if (!data->current_open_rsan.empty()) {
    const symafl::ShmNode &n = shm->nodes[data->current_open_rsan[0]];
    const symafl::ShmClosure *c = shm_clos(shm, n);
    fprintf(stderr, "[sedbt] attached closures=%zu s=",
            data->current_open_rsan.size());
    if (c) {
      for (uint16_t i = 0; i < c->s_n && i < 8; ++i)
        fprintf(stderr, "%s%u", i ? "," : "", shm->s_offs[c->s_off + i]);
    }
    fprintf(stderr, " node=%u %s\n", data->current_open_rsan[0],
            fname ? fname : "");
  }
}

static void first_contact(my_mutator_t *data, SeedLearn *st, const u8 *buf,
                          uint32_t len, const char *fname, bool may_submit) {
  auto wr = analyzer_check(&data->analyzer, buf, len);
  merge_rsan(st, wr.rsan_nodes);
  if (wr.learned == symafl::kWalkFailKind) {
    st->learned = symafl::kWalkFail;
    return;
  }
  if (wr.learned == symafl::kWalkTerminal) {
    take_terminal(st, wr);
    return;
  }
  st->frontier = wr.frontier;
  st->dir = wr.dir;
  st->skip_cnt = wr.skip_cnt;
  st->have_frontier = 1;
  if (!may_submit) {
    st->learned = symafl::kRingFull;
    return;
  }
  if (!try_submit_learn(data, st, buf, len)) {
    fprintf(stderr, "[sedbt] analyzer ring full, learned=2 %s\n",
            fname ? fname : "");
  }
}

static void apply_suffix(my_mutator_t *data, SeedLearn *st, const u8 *buf,
                         uint32_t len) {
  auto wr = analyzer_check_suffix(&data->analyzer, buf, len, st->frontier,
                                  st->dir);
  merge_rsan(st, wr.rsan_nodes);
  if (wr.learned == symafl::kWalkTerminal) {
    take_terminal(st, wr);
    return;
  }
  if (wr.learned == symafl::kWalkFailKind) {
    st->learned = symafl::kWalkFail;
    return;
  }
  if (wr.learned != symafl::kWalkFrontier) return;
  // Own LearnJob may still be queued. Another seed may have filled the
  // recorded edge; this walk then stops at a deeper unexplored. Remember
  // that edge and stay learned=0 (or 2): do not submit another job.
  st->frontier = wr.frontier;
  st->dir = wr.dir;
  st->skip_cnt = wr.skip_cnt;
  st->have_frontier = 1;
}

static void load_seed_learn(my_mutator_t *data, const char *filename) {
  data->current_open_rsan.clear();
  data->current_path_s_off = 0;
  data->current_path_s_n = 0;
  data->current_path_s_cons_n = 0;
  data->parent_seed.clear();
  data->current_frontier = sedbt::kUnexplored;
  data->current_dir = 0;
  data->current_have_frontier = 0;
  data->current_learned = symafl::kWalkFail;
  if (data->afl) {
    data->afl->sedbt_skip_det = 0;
    data->afl->sedbt_havoc_pct = 100;
  }
  if (!filename) return;
  auto it = data->seed_learn.find(filename);
  if (it == data->seed_learn.end()) {
    std::vector<u8> buf;
    if (!read_queue_file(filename, &buf)) return;
    SeedLearn st;
    first_contact(data, &st, buf.data(), (uint32_t)buf.size(), filename, true);
    it = data->seed_learn.emplace(filename, std::move(st)).first;
  } else {
    SeedLearn &st = it->second;
    if (st.learned == symafl::kInFlight) {
      std::vector<u8> buf;
      if (read_queue_file(filename, &buf))
        apply_suffix(data, &st, buf.data(), (uint32_t)buf.size());
    } else if (st.learned == symafl::kRingFull) {
      std::vector<u8> buf;
      if (read_queue_file(filename, &buf) && data->analyzer.tree) {
        uint32_t nn =
            data->analyzer.tree->hdr.n_nodes.load(std::memory_order_acquire);
        uint32_t ch = sedbt::kUnexplored;
        if (st.frontier >= sedbt::kRoot && st.frontier < nn && st.dir <= 1)
          ch = __atomic_load_n(
              &data->analyzer.tree->nodes[st.frontier].child[st.dir],
              __ATOMIC_ACQUIRE);
        if (ch != sedbt::kUnexplored) {
          apply_suffix(data, &st, buf.data(), (uint32_t)buf.size());
          if (st.learned == symafl::kRingFull &&
              !try_submit_learn(data, &st, buf.data(), (uint32_t)buf.size())) {
            fprintf(stderr, "[sedbt] analyzer ring full, learned=2 %s\n",
                    filename);
          }
        } else if (!try_submit_learn(data, &st, buf.data(),
                                     (uint32_t)buf.size())) {
          fprintf(stderr, "[sedbt] analyzer ring full, learned=2 %s\n",
                  filename);
        }
      }
    }
  }
  collect_open(data, it->second, filename);
  data->current_learned = it->second.learned;
  {
    std::vector<u8> parent;
    if (read_queue_file(filename, &parent))
      data->parent_seed = std::move(parent);
  }
  {
    symafl::suffix_screen_cache_clear(&data->screen_cache);
    if (data->path_s_screen && data->current_have_frontier &&
        data->analyzer.tree && !data->parent_seed.empty()) {
      uint32_t sc_front = data->current_frontier;
      uint8_t sc_dir = data->current_dir;
      if (data->path_s_mode == sedbt::PathSMode::Full) {
        sc_front = sedbt::kRoot;
        sc_dir = 0;
      }
      symafl::suffix_screen_cache_build(
          &data->screen_cache, data->analyzer.tree, sc_front, sc_dir,
          data->parent_seed.data(), (uint32_t)data->parent_seed.size());
    }
  }
  if (data->afl) {
    const bool have_explore = data->mut_path_s && data->current_path_s_n > 0;
    const bool have_vuln = data->mut_closure && !data->current_open_rsan.empty();
    if ((data->current_learned == symafl::kReady) &&
        (have_explore || have_vuln)) {
      data->afl->sedbt_skip_det = 1;
      data->afl->sedbt_havoc_pct = (u8)data->havoc_pct;
    } else {
      data->afl->sedbt_skip_det = 0;
      data->afl->sedbt_havoc_pct = 100;
    }
  }
}

// Unique sanitizer crash: (signal, peek simplify_trace hash). Peek does not
// count as fsrv_cov_exec (direct afl_fsrv_run_target). A new unique con_san
// crash whose peek pattern was already seen on fsrv_cov is fsrv_cov_miss.
static void handle_san_crash(my_mutator_t *data, const u8 *buf, size_t len,
                             SanFrom from) {
  afl_forkserver_t *sfsrv = &data->afl->fsrv_san;
  int sig = 0;
  if (sfsrv->child_status != -1 && WIFSIGNALED(sfsrv->child_status)) {
    sig = WTERMSIG(sfsrv->child_status);
  }
  data->san_crashes += 1;
  bool peek_cov_crash = false;
  uint32_t ph = peek_cov_simplify(data, buf, len, &peek_cov_crash);
  uint64_t key = ((uint64_t)(uint32_t)sig << 32) |
                 (peek_cov_crash ? 0xffffffffu : ph);
  if (!data->san_crash_keys.insert(key).second) return;
  data->fsrv_san_crash += 1;
  data->san_crashes_saved += 1;
  if (from == kSanConSan && !peek_cov_crash &&
      data->seen_simplify.count(ph)) {
    data->fsrv_cov_miss += 1;
    data->path_s_san_cov_miss += 1;
  }
  if (!data->afl->out_dir) return;
  char *path = alloc_printf("%s/crashes/id:%06llu,sig:%02u,san",
                            data->afl->out_dir,
                            (unsigned long long)data->san_crash_seq++, sig);
  int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
  if (fd < 0) {
    PFATAL("cannot create sanitizer crash case %s", path);
  }
  ck_write(fd, const_cast<u8 *>(buf), len, path);
  close(fd);
  WARNF("sanitizer crash saved: %s (sig=%d)\n", path, sig);
  ck_free(path);
}

static bool run_sanitizer_on(my_mutator_t *data, const u8 *buf, size_t len,
                             SanFrom from) {
  if (data->afl->fsrv_san.fsrv_pid <= 0 || !buf || len == 0) return false;
  afl_fsrv_write_to_testcase(&data->afl->fsrv, const_cast<u8 *>(buf), len);
  const uint64_t t0 = profile_now();
  fsrv_run_result_t sres = afl_fsrv_run_target(
      &data->afl->fsrv_san, data->afl->fsrv_san.exec_tmout,
      &data->afl->stop_soon);
  data->fsrv_san_ns += profile_now() - t0;
  data->fsrv_san_exec += 1;
  data->san_run_calls += 1;
  if (from == kSanConSan) {
    data->con_san_cnt += 1;
    data->path_s_san_exec += 1;
  }
  if (sres == FSRV_RUN_CRASH) {
    handle_san_crash(data, buf, len, from);
    return true;
  }
  if (sres == FSRV_RUN_TMOUT) {
    data->san_tmouts += 1;
  }
  return false;
}

static void run_path_s_san_candidate(my_mutator_t *data, const u8 *buf,
                                     size_t len) {
  bool crashed = run_sanitizer_on(data, buf, len, kSanConSan);
  if (crashed) data->path_s_san_crash += 1;
}

extern "C" void afl_custom_post_run(my_mutator_t *data) {
  const bool mutant = data->last_cov_candidate;
  data->last_cov_candidate = false;
  afl_forkserver_t *fsrv = &data->afl->fsrv;
  u32 n = fsrv->real_map_size ? fsrv->real_map_size : fsrv->map_size;
  if (n > fsrv->map_size) n = fsrv->map_size;
  uint32_t h = simplify_hash_bits(fsrv->trace_bits, n);
  const bool is_new = data->seen_simplify.insert(h).second;
  if (mutant && is_new) {
    data->cov_gain_cnt += 1;
    if (!data->last_cov_buf.empty()) {
      run_sanitizer_on(data, data->last_cov_buf.data(),
                       data->last_cov_buf.size(), kSanCovGain);
    }
  }
}

extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  if (!data->seeds_flushed) {
    data->seeds_flushed = true;
    if (!analyzer_wait_tree_ready(&data->analyzer)) {
      FATAL("analyzer TREE_READY failed");
    }
    if (data->analyzer.tree) {
      data->path_s_mode =
          (sedbt::PathSMode)data->analyzer.tree->hdr.path_s_mode;
      data->mut_path_s = data->path_s_mode != sedbt::PathSMode::Off;
    }
    for (const std::string &seed : data->pending_seeds) {
      std::vector<u8> buf;
      if (!read_queue_file(seed.c_str(), &buf)) continue;
      SeedLearn st;
      first_contact(data, &st, buf.data(), (uint32_t)buf.size(), seed.c_str(),
                    true);
      fprintf(stderr, "[sedbt] analyzer seed learned=%u %s\n", st.learned,
              seed.c_str());
      data->seed_learn[seed] = std::move(st);
    }
    data->pending_seeds.clear();
    if (!analyzer_ack(&data->analyzer) || !analyzer_wait_done(&data->analyzer)) {
      FATAL("analyzer bootstrap ACK/DONE failed");
    }
  }
  data->bootstrap_done = true;
  if (data->concolic_deadline && !data->phase_start) {
    data->phase_start = time(nullptr);
  }
  load_seed_learn(data, filename ? (const char *)filename : nullptr);
  return 1;
}

// AFL++ calls this before its normal save/queue path for a SymAFL probe. The
// probe result is measured against a temporary virgin bitmap in AFL++, then
// retained outside the queue for replay diagnostics. It never updates the
// SEDBT, AFL virgin_bits, scheduler queue, or admitted-gain counters.
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
  data->last_gained = true;
  SeedLearn st;
  first_contact(data, &st, buf.data(), (uint32_t)buf.size(), fname, true);
  data->seed_learn[fname] = std::move(st);
  return 0;
}

/// Havoc / AFL mutants run concrete (ADR 0009). A focused e_use-passer skips
/// the concrete forkserver: post_process runs fsrv_san and returns 0 so
/// write_to_testcase does not exec the coverage binary. Changing a tainted
/// GEP-index pin (SYMAFL_PATH_S_CONS_SAN) does the same for path-s explore
/// and for AFL det/havoc vs the queue parent, once per distinct GEP-byte
/// tuple, independent of MUT_PATH_S / PATH_S_SCREEN, and does not
/// CloseUnexplored. A sanitizer
/// crash then peeks fsrv_cov (no virgin update); path_s_san_cov_miss counts
/// inputs cov-first would drop.
extern "C" size_t afl_custom_post_process(my_mutator_t *data, u8 *buf,
                                          size_t buf_size, u8 **out_buf) {
  data->profile_exec_armed = false;
  data->afl->sedbt_probe_active = 0;
  data->afl->sedbt_candidate_kind = SEDBT_CANDIDATE_NONE;
  data->last_was_probe = false;
  data->replay_run_done = false;
  data->last_node = sedbt::kUnexplored;

  const bool focused = data->focused_pending;
  const bool from_path_s = data->path_s_pending;
  const bool path_s_san = data->path_s_san_pending;
  const uint32_t focused_node = data->focused_rsan_node;
  data->focused_pending = false;
  data->path_s_pending = false;
  data->path_s_san_pending = false;
  data->focused_rsan_node = ~0u;
  if (focused) {
    *out_buf = buf;
    if (buf && buf_size > 0) {
      const uint64_t t0 = profile_now();
      bool crashed = run_sanitizer_on(data, buf, buf_size, kSanFocused);
      data->vuln_ns += profile_now() - t0;
      if (crashed) close_focused_bug(data, focused_node);
    }
    return 0;
  }
  if (path_s_san) {
    *out_buf = buf;
    if (buf && buf_size > 0) run_path_s_san_candidate(data, buf, buf_size);
    return 0;
  }
  // AFL det/havoc: same GEP CONS_SAN gate vs the queue parent (independent
  // of path-s explore). Mutator-produced path-s candidates already decided.
  if (!from_path_s &&
      cons_san_should_skip(data, data->parent_seed.data(),
                           data->parent_seed.size(), buf, buf_size) &&
      data->afl->fsrv_san.fsrv_pid > 0) {
    *out_buf = buf;
    if (buf && buf_size > 0) run_path_s_san_candidate(data, buf, buf_size);
    return 0;
  }
  if (!from_path_s) data->default_exec += 1;

  data->screened += 1;
  data->admitted += 1;
  data->profile_exec_armed = data->profile_enabled;
  data->afl->sedbt_candidate_kind = SEDBT_CANDIDATE_ADMIT;
  data->vetoes_since_admit = 0;
  data->last_gained = false;
  data->last_dir = 0;
  write_progress(data, false);
  *out_buf = buf;
  if (buf && buf_size > 0) mark_cov_candidate(data, buf, buf_size);
  return buf_size;
}

extern "C" const char *afl_custom_introspection(my_mutator_t *data) {
  static char buf[2048];
  const sedbt::Tree &t = data->tree;
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
           "learn_skip_san=%llu "
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
           (unsigned long long)data->learn_skip_san_crash,
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
