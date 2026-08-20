//===-- dfsan_flags.inc -----------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// DFSan runtime flags.
//
//===----------------------------------------------------------------------===//
#ifndef DFSAN_FLAG
# error "Define DFSAN_FLAG prior to including this file!"
#endif

// DFSAN_FLAG(Type, Name, DefaultValue, Description)
// See COMMON_FLAG in sanitizer_flags.inc for more details.

DFSAN_FLAG(bool, warn_unimplemented, true,
           "Whether to warn on unimplemented functions.")
DFSAN_FLAG(bool, warn_nonzero_labels, false,
           "Whether to warn on unimplemented functions.")
DFSAN_FLAG(
    bool, strict_data_dependencies, true,
    "Whether to propagate labels only when there is an obvious data dependency"
    "(e.g., when comparing strings, ignore the fact that the output of the"
    "comparison might be data-dependent on the content of the strings). This"
    "applies only to the custom functions defined in 'custom.c'.")
DFSAN_FLAG(const char *, dump_labels_at_exit, "", "The path of the file where "
                                                  "to dump the labels when the "
                                                  "program terminates.")
DFSAN_FLAG(const char *, taint_file, "", "The path of the file which "
                                         "will be tainted.")
DFSAN_FLAG(size_t, taint_max_len, 0,
           "SymAFL v2 (forkserver mode): pre-create input-byte labels up to "
           "this many bytes, and tolerate the taint file not existing at "
           "process init (afl-fuzz creates .cur_input per run). 0 = stock "
           "behavior.")
DFSAN_FLAG(const char *, taint_socket, "", "The network source which "
                                          "will be tainted.")
DFSAN_FLAG(const char *, union_table, "union.txt", "union table.")
DFSAN_FLAG(int, shm_fd, -1, "shared union table.")
DFSAN_FLAG(const char *, shm_name, "", "shared union table by key.")
DFSAN_FLAG(size_t, shm_size, 0, "shared union table size.")
DFSAN_FLAG(int, pipe_fd, -1, "communication pipe fd.")
DFSAN_FLAG(int, trace_skip_depth, -1,
           "SymAFL v2 suffix tracing: suppress pipe condition events through "
           "this symbolic depth; -1 emits the complete trace.")
DFSAN_FLAG(const char *, single_pass_name, "",
           "SymAFL v2 single-pass capture shared event buffer.")
DFSAN_FLAG(size_t, single_pass_size, 0,
           "SymAFL v2 single-pass capture shared event buffer size.")
DFSAN_FLAG(const char *, pipe_name, "", "communication pipe filename.")
DFSAN_FLAG(int, control_pipe_fd, -1, "control pipe fd.")
DFSAN_FLAG(const char *, control_pipe_name, "", "control pipe filename.")
DFSAN_FLAG(bool, trace_bounds, false, "trace bounds info.")
// SymAFL/SEDBT: never return freed blocks to the libc freelist. Address reuse
// makes dict/pool/hash-chain layout depend on free order rather than on the
// input alone, which poisons SEDBT event order (libxml2 cid_mismatch class).
// Default on; set no_reuse_heap=false to restore stock free/realloc. Child
// processes exit after one run under the forkserver, so arena growth is bounded
// by a single execution. Compatible with (and weaker than) trace_bounds.
DFSAN_FLAG(bool, no_reuse_heap, true,
           "Do not return freed heap blocks to the allocator freelist.")
DFSAN_FLAG(bool, trace_fsize, false, "trace file size.")
DFSAN_FLAG(bool, exit_on_memerror, true, "terminate on memory error.")
DFSAN_FLAG(bool, solve_ub, false, "solve undefined behavior.")
DFSAN_FLAG(bool, allow_zero_size_alloc, false,
           "Allow malloc-size minimization to solve allocation sizes to zero.")
DFSAN_FLAG(bool, debug, false, "Print debug output.")
DFSAN_FLAG(const char *, output_dir, ".", "The path for output file.")
DFSAN_FLAG(int, instance_id, 0, "instance id for multi-instance fuzzing.")
DFSAN_FLAG(int, session_id, 0, "session/round id.")
DFSAN_FLAG(bool, force_stdin, false, "force tainting stdin.")
DFSAN_FLAG(bool, enum_gep, false, "enable GEP index enumeration.")
DFSAN_FLAG(int, string_map_capacity, 256, "initial capacity for string label maps.")
DFSAN_FLAG(bool, taint_trace_addr_cond, true,
           "SymAFL v2: emit equality constraints for tainted pointer indexes "
           "(GEP __taint_trace_gep) and tainted indirect-call/indirectbr "
           "targets (__taint_trace_indcall), so the SEDBT diverges when a "
           "mutated input selects a different array element or jump target.")
