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
  uint32_t mode = __atomic_load_n(&__single_pass->mode, __ATOMIC_ACQUIRE);
  return mode == SYMAFL_TRACE_FULL_STREAM ||
         mode == SYMAFL_TRACE_SUFFIX_PIPE;
}

//===----------------------------------------------------------------------===//
// PCBT trace folding
//===----------------------------------------------------------------------===//
//
// Long test inputs (e.g. a 64 KiB line without '\n') make getc loops emit one
// condition event per byte (up to ~131K events), which dominates the pipe
// transfer and the mutator's AST building. Strictly consecutive events that
// share the same cid, result, and predicate shape whose only Read/EofRead leaf
// advances by one byte are collapsed into a single fold frame; the mutator
// expands it back into one tree node per event. Loop-bound comparisons against
// flen_count labels repeat the exact same label and are folded the same way.
// There is only one pending frame: any event that interrupts a run flushes it
// before being written or becoming a new run, preserving execution order.
// Folding happens after the skip-depth filter, so the logical event count (used
// for skip_depth and tree depth) is unchanged; the SHM event_count only counts
// actual slots (a fold frame is one slot).

namespace {

// FOLD_OFFSET: getc-style conditions whose single Read/EofRead leaf advances
// by one byte per event (`c != EOF`, `c == '\n'`).
// FOLD_CONST: loop-bound conditions whose constant side (the loop counter,
// e.g. `i < n` with n = fread count) advances by one per event.
enum FoldKind { FOLD_NONE = 0, FOLD_OFFSET, FOLD_CONST };

struct FoldSlot {
  uint32_t cid;
  dfsan_label first_label;
  uint32_t last_offset;
  uintptr_t addr;
  uint32_t context;
  uint8_t result;
  uint16_t count;
  uint64_t shape_hash;
  FoldKind kind;
  bool valid;
};

// Only one run may remain pending. A fold frame cannot represent interleaved
// events from multiple shapes, so keeping several slots would reorder them
// when the slots are flushed later.
static FoldSlot g_fold_slot;

// FNV-1a 64-bit mixing, byte-wise.
static inline void fold_mix(uint64_t &h, uint64_t v) {
  for (int i = 0; i < 8; ++i) {
    h ^= (v >> (8 * i)) & 0xff;
    h *= 1099511628211ull;
  }
}

// Classifies a condition label as foldable. FOLD_OFFSET: ICmp between a
// concrete constant and a Read-family chain (ZExt(Read(8)) / raw Read(8) /
// flen_eof) with exactly one Read/EofRead leaf; *offset is the leaf position
// and *shape_hash fingerprints the structure without the fold dimension
// (constant-side values and the leaf offset are excluded). FOLD_CONST:
// comparisons whose symbolic side is a flen_count-family label (loop bounds
// `i < n`); *offset carries the constant side (the loop counter), which
// advances by one per iteration. Anything else is not foldable: multi-leaf
// shapes (e.g. `c != buf[k+1]`) and expressions whose structure changes per
// iteration (e.g. `(value ^ i) & 1`) are never folded, because expanding
// them from a single first label would not reproduce the per-iteration
// predicate.
static FoldKind classify_fold(dfsan_label label, uint32_t *offset,
                              uint64_t *shape_hash) {
  const dfsan_label_info *info = get_label_info(label);
  uint16_t op = info->op & 0xff;
  // A bare flen_count-family label emitted as a condition (uncommon; loop
  // bounds usually arrive as `i < n` ICmps whose symbolic side is flen_count).
  if (op == flen_count || op == flen_count_neg1 ||
      op == flen_count_elems) {
    *offset = 0;
    *shape_hash = 0;
    return FOLD_CONST;
  }
  if (op != ICmp) return FOLD_NONE;

  // Exactly one concrete side and one symbolic side.
  dfsan_label sym;
  uint64_t con;
  if (info->l1 == 0 && info->l2 != 0) {
    sym = info->l2;
    con = info->op1.i;
  } else if (info->l2 == 0 && info->l1 != 0) {
    sym = info->l1;
    con = info->op2.i;
  } else {
    return FOLD_NONE;
  }

  const dfsan_label_info *s = get_label_info(sym);
  // Loop-bound comparisons (`i < n`, n = fread/read count): the symbolic side
  // is a fixed flen_count label; the constant side is the loop counter, which
  // advances by one per iteration and is the fold dimension.
  if (s->op == flen_count || s->op == flen_count_neg1 ||
      s->op == flen_count_elems) {
    *offset = (uint32_t)con;
    uint64_t h = 1469598103934665603ull;
    fold_mix(h, (uint64_t)(info->op >> 8));  // compare predicate
    fold_mix(h, (uint64_t)s->op);            // flen_count family
    *shape_hash = h;
    return FOLD_CONST;
  }

  uint64_t h = 1469598103934665603ull;  // FNV offset basis
  fold_mix(h, (uint64_t)(info->op >> 8));  // compare predicate
  // The constant-side value participates in the shape: clang may compile
  // several comparisons over one value into a switch sharing a single cid
  // (e.g. `c != EOF` vs `c == ';'`), and the two shapes must accumulate in
  // separate slots. For byte-advancing conditions the constant side is fixed
  // per IR instruction, so this does not disturb the fold dimension.
  fold_mix(h, con);

  if (s->op == flen_eof && s->size == 32) {
    *offset = s->op1.i;
    fold_mix(h, (uint64_t)flen_eof);
    *shape_hash = h;
    return FOLD_OFFSET;
  }
  if (s->op == ZExt && s->size == 32) {
    const dfsan_label_info *r = get_label_info(s->l1);
    if (r->op == 0 && r->size == 8) {
      *offset = r->op1.i;
      fold_mix(h, (uint64_t)ZExt);
      *shape_hash = h;
      return FOLD_OFFSET;
    }
    return FOLD_NONE;
  }
  if (s->op == 0 && s->size == 8) {
    *offset = s->op1.i;
    fold_mix(h, 0);
    *shape_hash = h;
    return FOLD_OFFSET;
  }
  return FOLD_NONE;
}

// Writes one fold frame carrying the slot's sequence. Failures are tolerated
// (no Die): this can run at child exit when the reader is already gone.
static void write_fold_frame(uint32_t cid, dfsan_label label, uint8_t result,
                             uint16_t count, uintptr_t addr,
                             uint32_t context) {
  uint32_t trace_mode = __single_pass
      ? __atomic_load_n(&__single_pass->mode, __ATOMIC_ACQUIRE)
      : (__pipe_fd >= 0 ? SYMAFL_TRACE_FULL_STREAM : SYMAFL_TRACE_OFF);
  if (trace_mode == SYMAFL_TRACE_SUFFIX_SHM &&
      __atomic_load_n(&__single_pass->armed, __ATOMIC_ACQUIRE)) {
    if (__atomic_load_n(&__single_pass->overflow, __ATOMIC_ACQUIRE)) return;
    uint32_t index = __atomic_fetch_add(&__single_pass->event_count, 1,
                                        __ATOMIC_RELAXED);
    if (index >= __single_pass->event_capacity) {
      __atomic_store_n(&__single_pass->overflow, 1, __ATOMIC_RELEASE);
      return;
    }
    // A singleton sequence is an ordinary event, not a fold frame (the
    // decoder rejects count < 2).
    uint16_t wire_count = count == 1 ? 0 : count;
    __single_pass->events[index] = {cid, label, result, 0, wire_count, 0};
    return;
  }
  if (trace_mode != SYMAFL_TRACE_FULL_STREAM &&
      trace_mode != SYMAFL_TRACE_SUFFIX_PIPE) {
    return;
  }
  if (__pipe_fd < 0) return;
  // A singleton sequence is an ordinary event, not a fold frame (the decoder
  // rejects count < 2).
  bool singleton = count == 1;
  uint16_t wire_type = (uint16_t)(singleton ? cond_type : fold_type);
  uint32_t wire_count = singleton ? 0u : (uint32_t)count;
  pipe_msg msg = {
    .msg_type = wire_type,
    .flags = 0,
    .instance_id = __instance_id,
    .addr = addr,
    .context = context,
    .id = cid,
    .label = label,
    .result = result,
    .count = wire_count,
  };
  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    // Ignore (EPIPE during exit flush).
  }
}

static void flush_slot() {
  FoldSlot &s = g_fold_slot;
  if (!s.valid || s.count == 0) return;
  write_fold_frame(s.cid, s.first_label, s.result, s.count, s.addr,
                   s.context);
  s.valid = false;
}

// Returns true when the event was absorbed (folded into a pending sequence
// or stored as its start); the caller must then skip writing it. Only a
// strictly consecutive run may remain pending; an interrupt is flushed first.
static bool fold_absorb(dfsan_label label, uint8_t result, uint8_t loop_flag,
                        uint32_t cid, void *addr) {
  if (loop_flag & ConstraintFlag) {
    flush_slot();
    return false;
  }
  uint32_t offset = 0;
  uint64_t h = 0;
  FoldKind kind = classify_fold(label, &offset, &h);
  if (kind == FOLD_NONE) {
    flush_slot();
    return false;
  }

  FoldSlot &s = g_fold_slot;
  if (s.valid && s.cid == cid && s.shape_hash == h &&
      s.result == result && s.count < SYMAFL_MAX_FOLD_COUNT &&
      offset == s.last_offset + 1) {
    s.count += 1;
    s.last_offset = offset;
    return true;
  }
  // A fold frame cannot represent interleaved events. Emit the previous run
  // before storing this event so the wire order matches execution order.
  flush_slot();
  s.valid = true;
  s.cid = cid;
  s.kind = kind;
  s.first_label = label;
  s.last_offset = offset;
  s.shape_hash = h;
  s.result = result;
  s.count = 1;
  s.addr = (uintptr_t)addr;
  s.context = __taint_trace_callstack;
  return true;
}

}  // namespace

extern "C" void __dfsan_flush_trace_fold() {
  if (!__single_pass && __pipe_fd < 0) return;
  flush_slot();
}

//===----------------------------------------------------------------------===//
// Shared Helper Functions
//===----------------------------------------------------------------------===//

extern "C" void __taint_send_cond(dfsan_label label, uint8_t result,
                                  uint8_t add_nested, uint8_t loop_flag,
                                  uint32_t cid, void *addr) {
  // Only input-dependent, initialized labels are symbolic PCBT events. Keep
  // this guard at the transport boundary as well as in fastgen.cpp because
  // runtime custom hooks also call __taint_send_cond directly.
  if (label == 0 || label == kInitializingLabel) return;
  // Heap-layout conditions (pointer/pointer-diff compares, including
  // pool-freespace vs namelen) are path-local under allocator state. Emitting
  // them as PCBT events creates site-dependent cid pairs at the same depth
  // (libxml2 dict.c:233 AddString pool walk vs dict.c:865 hash lookup).
  // ConstraintFlag events (fread length) always pass.
  if (!(loop_flag & ConstraintFlag) && taint_is_heap_layout_cond(label))
    return;

  // AFL's SymAFL extension selects one of four per-child modes through the
  // shared control block. FULL_STREAM writes bootstrap events to the pipe;
  // SUFFIX_SHM writes the normal post-frontier suffix to bounded shared memory;
  // SUFFIX_PIPE is the overflow-replay fallback and writes that suffix to pipe.
  // Standalone launcher/direct tracing has no single-pass control block.
  // Preserve its established pipe semantics: a configured pipe is a full
  // event stream. The control block is only present for forkserver runs,
  // where the mutator explicitly selects OFF, FULL_STREAM, SUFFIX_SHM, or
  // SUFFIX_PIPE.
  uint32_t trace_mode = __single_pass
      ? __atomic_load_n(&__single_pass->mode, __ATOMIC_ACQUIRE)
      : (__pipe_fd >= 0 ? SYMAFL_TRACE_FULL_STREAM : SYMAFL_TRACE_OFF);
  if (trace_mode == SYMAFL_TRACE_SUFFIX_SHM &&
      __atomic_load_n(&__single_pass->armed, __ATOMIC_ACQUIRE)) {
    if (label == 0 || label == kInitializingLabel) return;
    if (++__taint_symbolic_depth <= __single_pass->skip_depth) return;
    // Once the bounded suffix buffer has overflowed, this child must not
    // touch the event array again. The mutator will discard the partial
    // suffix and replay this coverage-gaining input through pipe-suffix.
    if (__atomic_load_n(&__single_pass->overflow, __ATOMIC_ACQUIRE)) return;
    // Collapse long runs of byte-advancing conditions into fold frames.
    if (fold_absorb(label, result, loop_flag, cid, addr)) return;
    uint32_t index = __atomic_fetch_add(&__single_pass->event_count, 1,
                                        __ATOMIC_RELAXED);
    if (index >= __single_pass->event_capacity) {
      __atomic_store_n(&__single_pass->overflow, 1, __ATOMIC_RELEASE);
      return;
    }
    uint8_t constraint = (loop_flag & ConstraintFlag) ? 1 : 0;
    __single_pass->events[index] = {cid, label, result, constraint, 0, 0};
    return;
  }

  if (trace_mode != SYMAFL_TRACE_FULL_STREAM &&
      trace_mode != SYMAFL_TRACE_SUFFIX_PIPE) {
    return;
  }

  if (__pipe_fd < 0) return;

  // Pipe suffix replay keeps concolic execution and AST construction intact;
  // it only suppresses already-known PCBT prefix condition events. The
  // forkserver cannot reparse TAINT_OPTIONS for every child, so use the shared
  // skip depth in that case. The flag remains for standalone launcher tracing.
  int skip_depth = flags().trace_skip_depth;
  if (trace_mode == SYMAFL_TRACE_SUFFIX_PIPE) {
    skip_depth = static_cast<int>(__single_pass->skip_depth);
  }
  if (skip_depth >= 0) {
    if (label == 0 || label == kInitializingLabel) return;
    if (++__taint_symbolic_depth <=
        static_cast<uint64_t>(skip_depth)) {
      return;
    }
  }

  // Collapse long runs of byte-advancing conditions into fold frames.
  if (fold_absorb(label, result, loop_flag, cid, addr)) return;

  uint16_t flags = 0;
  if (add_nested) flags |= F_ADD_CONS;
  if (loop_flag & ConstraintFlag) flags |= F_CONSTRAINT;

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
    .result = result,
    .count = 0
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }
}
