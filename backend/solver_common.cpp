/*
  Common code shared between fastgen and thoroupy solvers.

   ------------------------------------------------

   Written by Chengyu Song <csong@cs.ucr.edu> and
              Ju Chen <jchen757@ucr.edu>

   Copyright 2021-2025 UC Riverside. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

 */

#include "solver_common.h"

#include <fcntl.h>
#include <string.h>
#include <sys/mman.h>

//===----------------------------------------------------------------------===//
// Shared Global State
//===----------------------------------------------------------------------===//

uint32_t __instance_id;
uint32_t __session_id;
int __pipe_fd;
int __control_pipe_fd;
static uint64_t __taint_symbolic_depth;
static symafl_single_pass_control *__single_pass;

void InitializeSinglePassCapture() {
  if (internal_strcmp(flags().single_pass_name, "") == 0) return;
  if (flags().single_pass_size < sizeof(symafl_single_pass_control)) {
    Printf("FATAL: invalid single-pass capture size %zu\n",
           flags().single_pass_size);
    Die();
  }

  int fd = shm_open(flags().single_pass_name, O_RDWR, S_IRUSR | S_IWUSR);
  if (fd == -1) {
    Printf("FATAL: cannot open single-pass capture buffer\n");
    Die();
  }
  uptr mapped = internal_mmap(nullptr, flags().single_pass_size,
                              PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  internal_close(fd);
  int err;
  if (internal_iserror(mapped, &err)) {
    Printf("FATAL: cannot map single-pass capture buffer: %s\n",
           strerror(err));
    Die();
  }
  __single_pass = reinterpret_cast<symafl_single_pass_control *>(mapped);
  if (__single_pass->magic != SYMAFL_SINGLE_PASS_MAGIC ||
      __single_pass->version != SYMAFL_SINGLE_PASS_VERSION ||
      symafl_single_pass_size(__single_pass->event_capacity) >
          flags().single_pass_size) {
    Printf("FATAL: invalid single-pass capture header\n");
    Die();
  }
}

bool IsTraceStreamEnabled() {
  if (__pipe_fd < 0) return false;
  if (!__single_pass) return true;
  return __atomic_load_n(&__single_pass->mode, __ATOMIC_ACQUIRE) ==
         SYMAFL_TRACE_FULL_STREAM;
}

//===----------------------------------------------------------------------===//
// Shared Helper Functions
//===----------------------------------------------------------------------===//

void __taint_send_cond(dfsan_label label, uint8_t result,
                       uint8_t add_nested, uint8_t loop_flag,
                       uint32_t cid, void *addr) {

  // AFL's SymAFL extension selects one of three per-child modes through the
  // shared control block. FULL_STREAM falls through to the regular pipe path;
  // SUFFIX_SHM writes only the post-frontier symbolic suffix to shared memory.
  // Standalone launcher/direct tracing has no single-pass control block.
  // Preserve its established pipe semantics: a configured pipe is a full
  // event stream. The control block is only present for forkserver runs,
  // where the mutator explicitly selects OFF, FULL_STREAM, or SUFFIX_SHM.
  uint32_t trace_mode = __single_pass
      ? __atomic_load_n(&__single_pass->mode, __ATOMIC_ACQUIRE)
      : (__pipe_fd >= 0 ? SYMAFL_TRACE_FULL_STREAM : SYMAFL_TRACE_OFF);
  if (trace_mode == SYMAFL_TRACE_SUFFIX_SHM &&
      __atomic_load_n(&__single_pass->armed, __ATOMIC_ACQUIRE)) {
    if (label == 0 || label == kInitializingLabel) return;
    if (++__taint_symbolic_depth <= __single_pass->skip_depth) return;
    uint32_t index = __atomic_fetch_add(&__single_pass->event_count, 1,
                                        __ATOMIC_RELAXED);
    if (index >= __single_pass->event_capacity) {
      __atomic_store_n(&__single_pass->overflow, 1, __ATOMIC_RELEASE);
      return;
    }
    __single_pass->events[index] = {cid, label, result, {0, 0, 0}};
    return;
  }

  if (trace_mode != SYMAFL_TRACE_FULL_STREAM) return;

  if (__pipe_fd < 0) return;

  // Suffix tracing keeps the concolic execution and AST construction intact;
  // it only removes already-known PCBT prefix events from the pipe. Match the
  // mutator's tree-event definition exactly: concrete and initializing labels
  // never count toward symbolic depth.
  if (flags().trace_skip_depth >= 0) {
    if (label == 0 || label == kInitializingLabel) return;
    if (++__taint_symbolic_depth <=
        static_cast<uint64_t>(flags().trace_skip_depth)) {
      return;
    }
  }

  uint16_t flags = 0;
  if (add_nested) flags |= F_ADD_CONS;

  // set the loop flags according to branching results
  switch (loop_flag) {
    case TrueBranchLoopExit:
      flags |= result ? F_LOOP_EXIT : F_LOOP_LATCH;
      break;
    case TrueBranchLoopLatch:
      flags |= result ? F_LOOP_LATCH : F_LOOP_EXIT;
      break;
    case FalseBranchLoopExit:
      flags |= result ? F_LOOP_LATCH : F_LOOP_EXIT;
      break;
    case FalseBranchLoopLatch:
      flags |= result ? F_LOOP_EXIT : F_LOOP_LATCH;
      break;
    default:
      // No loop flag or unrecognized flag, do nothing
      break;
  }

  // send info
  pipe_msg msg = {
    .msg_type = cond_type,
    .flags = flags,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .id = cid,
    .label = label,
    .result = result
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }
}
