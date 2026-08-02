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
  bool last_was_probe = false;
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
                              uint8_t *dir) {
  uint64_t start = profile_start(data);
  bool admitted = data->tree.CheckInput(buf, buf_size, node, dir,
                                        data->rlimit);
  profile_stop(data, start, &data->profile_check_ns,
               &data->profile_check_calls);
  return admitted;
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
  if (getenv("SYMAFL_PROFILE")) {
    data->profile_enabled = true;
    fprintf(stderr, "[pcbt] profiling enabled (SYMAFL_PROFILE=1)\n");
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
  return data;
}

extern "C" void afl_custom_deinit(my_mutator_t *data) {
  const pcbt::Tree &t = data->tree;
  fprintf(stderr,
          "[pcbt] traces=%llu nodes=%llu pred_nodes=%llu depth=%llu conflicts=%llu "
          "opaque=%llu failed=%llu timeouts=%llu memerr=%llu screened=%llu "
          "admitted=%llu vetoed=%llu saturated=%llu "
          "single_pass=%llu single_pass_overflow=%llu "
          "admit_empty=%llu admit_opaque=%llu admit_eval_failure=%llu admit_frontier=%llu "
          "admit_too_short=%llu "
          "veto_terminal=%llu veto_rlimit=%llu probe_admitted=%llu probe_gained=%llu profile=%d "
          "check_ns=%llu check_calls=%llu trace_ns=%llu trace_calls=%llu "
          "replay_ns=%llu replay_calls=%llu\n",
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
          (unsigned long long)(data->screening ? 0 : 1),
          (unsigned long long)data->single_pass_captures,
          (unsigned long long)data->single_pass_overflows,
          (unsigned long long)t.check_admit_empty,
          (unsigned long long)t.check_admit_opaque,
          (unsigned long long)t.check_admit_eval_failure,
          (unsigned long long)t.check_admit_frontier,
          (unsigned long long)t.check_admit_too_short,
          (unsigned long long)t.check_veto_terminal,
          (unsigned long long)t.check_veto_rlimit,
          (unsigned long long)data->veto_probe_admitted,
          (unsigned long long)data->veto_probe_gained,
          (int)(data->profile_enabled ? 1 : 0),
          (unsigned long long)data->profile_check_ns,
          (unsigned long long)data->profile_check_calls,
          (unsigned long long)data->profile_trace_ns,
          (unsigned long long)data->profile_trace_calls,
          (unsigned long long)data->profile_replay_ns,
          (unsigned long long)data->profile_replay_calls);
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
  delete data;
}


static void disarm_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELEASE);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_OFF, __ATOMIC_RELEASE);
  data->single_pass_armed = false;
}

static void arm_full_capture(my_mutator_t *data) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_FULL_STREAM, __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->single_pass_armed = true;
}

static void arm_suffix_capture(my_mutator_t *data, pcbt::NodeRef node,
                               uint8_t dir) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  control->skip_depth = data->tree.depth(node);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_SUFFIX_SHM, __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->last_node = node;
  data->last_dir = dir;
  data->single_pass_armed = true;
}

static void arm_pipe_suffix_capture(my_mutator_t *data, pcbt::NodeRef node,
                                    uint8_t dir) {
  symafl_single_pass_control *control = data->single_pass_control;
  __atomic_store_n(&control->event_count, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->overflow, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&control->armed, 0, __ATOMIC_RELAXED);
  control->skip_depth = data->tree.depth(node);
  __atomic_store_n(&control->mode, SYMAFL_TRACE_SUFFIX_PIPE,
                   __ATOMIC_RELEASE);
  __atomic_store_n(&control->armed, 1, __ATOMIC_RELEASE);
  data->last_node = node;
  data->last_dir = dir;
  data->single_pass_armed = true;
}

static bool decode_full_stream(const u8 *wire, size_t wire_size,
                               std::vector<pcbt::Event> *events) {
  size_t offset = 0;
  while (offset < wire_size) {
    if (wire_size - offset < sizeof(pipe_msg)) return false;
    pipe_msg msg;
    memcpy(&msg, wire + offset, sizeof(msg));
    offset += sizeof(msg);
    if (msg.msg_type == cond_type) {
      if (msg.label != 0 && msg.label != kInitializingLabel) {
        if (msg.label >= MAX_LABEL) return false;
        events->push_back({msg.id, msg.label, (uint8_t)(msg.result != 0)});
      }
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
  return false;  // discard mismatched trace
}

static bool insert_full_stream(my_mutator_t *data, const u8 *buf,
                               size_t buf_size, const char *fname) {
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
                                            MAX_LABEL);
  data->traced_runs += 1;
  fprintf(stderr, "[pcbt-trace] %s mode=full events=%zu created=%u\n",
          fname, events.size(), created);
  disarm_capture(data);
  return true;
}

static bool insert_pipe_suffix_capture(my_mutator_t *data, const u8 *buf,
                                       size_t buf_size, const char *fname) {
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
      events, __dfsan_label_info, MAX_LABEL);
  fprintf(stderr,
          "[pcbt-trace] %s mode=pipe-suffix skip=%u events=%zu created=%u\n",
          fname, data->tree.depth(data->last_node), events.size(), created);
  disarm_capture(data);
  return true;
}

static bool insert_suffix_capture(my_mutator_t *data, const u8 *buf,
                                  size_t buf_size, const char *fname) {
  ProfileSegment trace_seg(data, &data->profile_trace_ns,
                           &data->profile_trace_calls);
  if (!data->single_pass_armed || data->last_node == pcbt::kUnexplored) {
    return false;
  }
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
  for (uint32_t i = 0; i < count; ++i) {
    const symafl_single_pass_event &event = control->events[i];
    if (event.label == 0 || event.label == kInitializingLabel ||
        event.label >= MAX_LABEL) {
      disarm_capture(data);
      return false;
    }
    events.push_back({event.cid, event.label, event.result});
  }
  uint32_t created = data->tree.InsertSuffix(data->last_node, data->last_dir,
      events, data->single_pass_label_info, MAX_LABEL);
  data->single_pass_captures += 1;
  fprintf(stderr,
          "[pcbt-trace] %s mode=suffix skip=%u events=%zu created=%u\n",
          fname, data->tree.depth(data->last_node), events.size(), created);
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

extern "C" void afl_custom_post_run(my_mutator_t *data) {
  if (data->bootstrap_done || !data->single_pass_armed) return;
  uint32_t mode = __atomic_load_n(&data->single_pass_control->mode,
                                  __ATOMIC_ACQUIRE);
  if (mode == SYMAFL_TRACE_SUFFIX_SHM &&
      data->last_node != pcbt::kUnexplored) {
    (void)insert_suffix_capture(data, nullptr, 0, "bootstrap");
  } else if (mode == SYMAFL_TRACE_FULL_STREAM) {
    (void)insert_full_stream(data, nullptr, 0, "bootstrap");
  }
  data->last_node = pcbt::kUnexplored;
}

extern "C" u8 afl_custom_queue_get(my_mutator_t *data, const u8 *filename) {
  (void)filename;
  data->bootstrap_done = true;
  return 1;
}

extern "C" u8 afl_custom_queue_new_entry(my_mutator_t *data,
                                         const u8 *filename_new_queue,
                                         const u8 *filename_orig_queue) {
  (void)filename_orig_queue;
  // A veto-probe that gained coverage: count it and leave the tree untouched.
  if (data->last_was_probe) {
    data->last_was_probe = false;
    data->veto_probe_gained += 1;
    data->last_gained = true;
    return 0;
  }
  if (!data->bootstrap_done || !data->single_pass_armed) return 0;
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
  uint8_t dir = data->last_dir;
  bool inserted = mode == SYMAFL_TRACE_SUFFIX_SHM
      ? insert_suffix_capture(data, buf.data(), buf.size(), fname)
      : mode == SYMAFL_TRACE_SUFFIX_PIPE
            ? insert_pipe_suffix_capture(data, buf.data(), buf.size(), fname)
            : mode == SYMAFL_TRACE_FULL_STREAM
                  ? insert_full_stream(data, buf.data(), buf.size(), fname)
                  : false;
  if (!inserted && node != pcbt::kUnexplored) {
    (void)replay_pipe_suffix(data, buf.data(), buf.size(), fname, node, dir);
  }
  data->last_gained = true;
  data->traced_entries.insert(fname);
  return 0;
}

/// PCBT screening: veto mutated candidates that cannot reach an unexplored
/// frontier. Returning 0 with *out_buf=NULL tells AFL++ to skip executing
/// this candidate entirely.
extern "C" size_t afl_custom_post_process(my_mutator_t *data, u8 *buf,
                                          size_t buf_size, u8 **out_buf) {
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

  if (!data->screening) {
    data->screened += 1;
    data->admitted += 1;
    *out_buf = buf;
    return buf_size;
  }

  data->screened += 1;
  pcbt::NodeRef node = pcbt::kUnexplored;
  uint8_t dir = 0;
  if (check_input_timed(data, buf, (uint32_t)buf_size, &node, &dir)) {
    data->admitted += 1;
    data->vetoes_since_admit = 0;
    data->last_gained = false;
    // Dry-run corpus paths must all enter the tree, so bootstrap is always
    // pipe-full. Thereafter a candidate has an established frontier and uses
    // SHM. The pipe is reserved for data that is known to be consumed: the
    // bootstrap trace or an overflow replay after AFL++ confirms a gain.
    // When replay_check is enabled, always use full-pipe so the complete
    // trace can be compared against the current tree before insertion.
    if (!data->bootstrap_done || data->replay_check ||
        node == pcbt::kUnexplored) {
      data->last_node = node;
      data->last_dir = dir;
      arm_full_capture(data);
    } else {
      arm_suffix_capture(data, node, dir);
    }
    *out_buf = buf;
    return buf_size;
  }

  data->vetoed += 1;
  ++data->vetoes_since_admit;
  // Veto probe: execute a sampled vetoed candidate to measure whether the
  // screening is incorrectly vetoing would-be coverage-gaining inputs. The
  // probe does not arm capture, so it never grows the tree; its coverage gain
  // (if any) is counted in veto_probe_gained.
  if (data->veto_probe_every &&
      ++data->veto_probe_count >= data->veto_probe_every) {
    data->veto_probe_count = 0;
    data->veto_probe_admitted += 1;
    data->last_was_probe = true;
    data->last_gained = false;
    data->last_node = pcbt::kUnexplored;
    if (data->single_pass_armed) disarm_capture(data);
    *out_buf = buf;
    return buf_size;
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
              "[pcbt] tree saturated after %llu vetoes; switching to concrete\n",
              (unsigned long long)data->vetoed);
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
           "screened=%llu admitted=%llu vetoed=%llu saturated=%llu "
           "single_pass=%llu single_pass_overflow=%llu "
           "admit_empty=%llu admit_opaque=%llu admit_eval_failure=%llu admit_frontier=%llu "
           "admit_too_short=%llu "
           "veto_terminal=%llu veto_rlimit=%llu probe_admitted=%llu probe_gained=%llu profile=%d "
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
           (unsigned long long)(data->screening ? 0 : 1),
           (unsigned long long)data->single_pass_captures,
           (unsigned long long)data->single_pass_overflows,
           (unsigned long long)t.check_admit_empty,
           (unsigned long long)t.check_admit_opaque,
           (unsigned long long)t.check_admit_eval_failure,
           (unsigned long long)t.check_admit_frontier,
           (unsigned long long)t.check_admit_too_short,
           (unsigned long long)t.check_veto_terminal,
           (unsigned long long)t.check_veto_rlimit,
           (unsigned long long)data->veto_probe_admitted,
           (unsigned long long)data->veto_probe_gained,
           (int)(data->profile_enabled ? 1 : 0),
           (unsigned long long)data->profile_check_ns,
           (unsigned long long)data->profile_check_calls,
           (unsigned long long)data->profile_trace_ns,
           (unsigned long long)data->profile_trace_calls,
           (unsigned long long)data->profile_replay_ns,
           (unsigned long long)data->profile_replay_calls);
  return buf;
}
