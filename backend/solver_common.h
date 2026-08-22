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

#ifndef SOLVER_COMMON_H
#define SOLVER_COMMON_H

#include "sanitizer_common/sanitizer_common.h"
#include "sanitizer_common/sanitizer_file.h"
#include "sanitizer_common/sanitizer_posix.h"
#include "dfsan/dfsan.h"

using namespace __dfsan;

//===----------------------------------------------------------------------===//
// Shared Global State
//===----------------------------------------------------------------------===//

extern uint32_t __instance_id;
extern uint32_t __session_id;
extern int __pipe_fd;
extern int __control_pipe_fd;

// Maps the optional shared single-pass capture control block. Called by every
// solver backend during runtime initialization.
void InitializeSinglePassCapture();
bool IsTraceStreamEnabled();

// filter, defined in dfsan.cpp
extern SANITIZER_INTERFACE_ATTRIBUTE THREADLOCAL uint32_t __taint_trace_callstack;

//===----------------------------------------------------------------------===//
// Shared Helper Functions
//===----------------------------------------------------------------------===//

// Note: get_const_result() is defined in dfsan.h

// Send conditional branch info to solver. extern "C": the dfsan runtime
// interceptors (dfsan_custom.cpp) also report events through this entry.
extern "C" void __taint_send_cond(dfsan_label label, uint8_t result,
                                  uint8_t add_nested, uint8_t loop_flag,
                                  uint32_t cid, void *addr);

// Mark the next __taint_send_cond as a tainted-GEP-index pin (F_GEP_PIN).
// Call immediately before the GEP equality send_cond; the flag is consumed
// once. Indcall / fread-style read-length ConstraintFlag events must not set
// this. memcpy-family size uses __taint_mark_next_cond_memlen_pin.
extern "C" void __taint_mark_next_cond_gep_pin();
extern "C" void __taint_mark_next_cond_memlen_pin();
extern "C" void __taint_trace_copy_len(dfsan_label len_label, uint64_t len,
                                       uint32_t cid);

#endif // SOLVER_COMMON_H
