/*
  The code is for out-of-process constraints solving with fastgen.

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

static inline void __send_ubi(dfsan_label label, uint64_t result,
                              uint32_t cid, void *addr) {
  if (!IsTraceStreamEnabled())
    return;

  pipe_msg msg = {
    .msg_type = memerr_type,
    .flags = F_MEMERR_UBI,
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

// Instrumented switch cases are reported as an ordered chain of ordinary
// equality decisions. The compiler emits all case hooks before the native
// switch, so once one comparison is true, later hooks are suppressed. The
// default path is represented by the false result of the last case; it has no
// synthetic event of its own.
static struct switch_true_case {
  uint32_t cid;       // in-flight switch's cid; 0 = no switch in flight
  bool matched = false;
} __switch_true_case = {0};

static void trace_cmp(dfsan_label op1, dfsan_label op2, uint32_t size,
                      uint32_t predicate, uint64_t c1, uint64_t c2,
                      uint32_t cid, bool switch_cmp) {
  if (op1 == 0 && op2 == 0)
    return;

  void *addr = __builtin_return_address(0);

  if (op1 == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", op1, addr);
    if (flags().solve_ub) __send_ubi(op1, c1, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }
  if (op2 == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", op2, addr);
    if (flags().solve_ub) __send_ubi(op2, c2, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }

  AOUT("solving cmp: %u %u %u %d %lu %lu 0x%x @%p\n",
       op1, op2, size, predicate, c1, c2, cid, addr);

  uint8_t r = get_const_result(c1, c2, predicate);
  dfsan_label temp = dfsan_union(op1, op2, (predicate << 8) | ICmp, size, c1, c2);

  if (switch_cmp && __switch_true_case.cid != cid) {
    // A switch's case hooks are consecutive in the instrumented stream.
    __switch_true_case.matched = false;
    __switch_true_case.cid = cid;
  }

  if (switch_cmp && __switch_true_case.matched)
    return;

  // Both ordinary comparisons and switch case comparisons are real binary
  // decisions. In particular, default consumes the final case's false edge.
  // Switch equality is a complete decision over the dispatch value. Keep it
  // as an ordinary wire event, but do not ask standalone solver frontends to
  // recursively add the shadow's unrelated memcpy/load subconstraints.
  __taint_send_cond(temp, r, 0, 0, cid, addr);

  if (switch_cmp && r) {
    __switch_true_case.matched = true;
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_cmp(dfsan_label op1, dfsan_label op2, uint32_t size,
                  uint32_t predicate, uint64_t c1, uint64_t c2,
                  uint32_t cid) {
  trace_cmp(op1, op2, size, predicate, c1, c2, cid, false);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_switch_cmp(dfsan_label op1, dfsan_label op2, uint32_t size,
                         uint32_t predicate, uint64_t c1, uint64_t c2,
                         uint32_t cid) {
  trace_cmp(op1, op2, size, predicate, c1, c2, cid, true);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_switch_end(uint32_t cid) {
  if (__switch_true_case.cid != cid) {
    return;
  }

  // The final case's false result is the default edge. There is no default
  // event to emit here; only discard the per-switch suppression state.
  __switch_true_case.cid = 0;
  __switch_true_case.matched = false;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_cond(dfsan_label label, bool r, uint8_t flag, uint32_t cid) {
  // Concrete conditions are not symbolic events. They must not reach the
  // transport or consume suffix-depth positions.
  if (label == 0)
    return;

  void *addr = __builtin_return_address(0);

  if (label == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", label, addr);
    if (flags().solve_ub) __send_ubi(label, r, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }

  AOUT("solving cond: %u %u 0x%x 0x%x %p\n",
       label, r, __taint_trace_callstack, cid, addr);

  uint8_t add_nested = flag & UndefinedCheck ? 0 : 1;
  uint8_t loop_flag = flag & LoopFlagMask;

  // always add nested
  __taint_send_cond(label, r, add_nested, loop_flag, cid, addr);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
__taint_trace_select(dfsan_label cond_label, dfsan_label true_label,
                     dfsan_label false_label, uint8_t r, uint8_t true_op,
                     uint8_t false_op, uint32_t cid) {
  if (cond_label == 0)
    return r ? true_label : false_label;

  void *addr = __builtin_return_address(0);

  if (cond_label == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", cond_label, addr);
    if (flags().solve_ub) __send_ubi(cond_label, r, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return r ? true_label : false_label;
  }

  AOUT("solving select: %u %u %u %u %u %u 0x%x @%p\n",
       cond_label, true_label, false_label, r, true_op, false_op, cid, addr);

  // check if it's actually a logical AND: select cond, label, false
  if (true_label != 0 && false_op == 0) {
    dfsan_label land = dfsan_union(cond_label, true_label, And, 1, r, true_op);
    uint8_t lr = (r && true_op) ? 1 : 0;
    __taint_send_cond(land, lr, 1, 0, cid, addr);
    return land;
  } else if (false_label != 0 && true_op == 1) {
    // logical OR: select cond, true, label
    dfsan_label lor = dfsan_union(cond_label, false_label, Or, 1, r, false_op);
    uint8_t lr = (r || false_op) ? 1 : 0;
    __taint_send_cond(lor, lr, 1, 0, cid, addr);
    return lor;
  } else {
    // normal select?
    AOUT("normal select?!\n");
    __taint_send_cond(cond_label, r, 1, 0, cid, addr);
    return r ? true_label : false_label;
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_indcall(dfsan_label label, uint64_t target, uint32_t cid) {
  if (label == 0)
    return;

  void *addr = __builtin_return_address(0);

  if (label == kInitializingLabel) {
    AOUT("WARNING: uninitialized label %u @%p\n", label, addr);
    if (flags().solve_ub) __send_ubi(label, target, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }

  AOUT("tainted indirect call/indirectbr target: %d = 0x%llx cid 0x%x\n",
       label, (unsigned long long)target, cid);

  // SymAFL v2: pin the tainted jump target to its observed concrete address
  // so the PCBT diverges when a mutated input reaches a different target.
  if (flags().taint_trace_addr_cond) {
    dfsan_label eq =
        dfsan_union(label, 0, (bveq << 8) | ICmp, 64, target, target);
    if (eq != 0 && eq != kInitializingLabel)
      __taint_send_cond(eq, 1, 0, ConstraintFlag, cid, addr);
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_gep(dfsan_label ptr_label, uint64_t ptr,
                  dfsan_label index_label, int64_t index,
                  uint64_t num_elems, uint64_t elem_size,
                  int64_t current_offset, uint32_t cid) {
  if (index_label == 0)
    return;

  void *addr = __builtin_return_address(0);

  if (index_label == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", index_label, addr);
    if (flags().solve_ub) __send_ubi(index_label, index, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }
  if (ptr_label == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", ptr_label, addr);
    if (flags().solve_ub) __send_ubi(ptr_label, ptr, cid, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }

  // SymAFL v2: pin the tainted index to its observed concrete value so the
  // PCBT diverges when a mutated input selects a different array element.
  // Reuses cond_type + PKind::equal (bveq); result is always 1 for the
  // traced run. Multiple GEPs (multi-index or load+store of a[i]+=f(a[i]))
  // correctly produce multiple constraint nodes: each access is a symbolic
  // data-state step. Do not collapse or suppress these as "duplicate noise".
  if (flags().taint_trace_addr_cond) {
    dfsan_label_info *idx_info = get_label_info(index_label);
    uint16_t width = idx_info->size;
    if (width != 0 && width <= 64) {
      uint64_t k = (width == 64)
                       ? (uint64_t)index
                       : ((uint64_t)index & ((1ULL << width) - 1));
      dfsan_label eq =
          dfsan_union(index_label, 0, (bveq << 8) | ICmp, width, k, k);
      if (eq != 0 && eq != kInitializingLabel)
        __taint_send_cond(eq, 1, 0, ConstraintFlag, cid, addr);
    }
  }

  AOUT("tainted GEP index: %ld = %d, ne: %ld, es: %ld, offset: %ld\n",
      index, index_label, num_elems, elem_size, current_offset);

  if (!IsTraceStreamEnabled())
    return;

  // send gep info, in two pieces
  pipe_msg msg = {
    .msg_type = gep_type,
    .flags = 0,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .label = index_label, // just in case
    .result = (uint64_t)index
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }

  gep_msg gmsg = {
    .ptr_label = ptr_label,
    .index_label = index_label,
    .ptr = ptr,
    .index = index,
    .num_elems = num_elems,
    .elem_size = elem_size,
    .current_offset = current_offset
  };

  // FIXME: assuming single writer so msg will arrive in the same order
  if (internal_write(__pipe_fd, &gmsg, sizeof(gmsg)) < 0) {
    Die();
  }

  return;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_offset(dfsan_label offset_label, s64 offset, unsigned size) {
  // use add_constraint_type to send offset constraints
  if (offset_label == 0)
    return;

  void *addr = __builtin_return_address(0);

  AOUT("tainted offset: %ld = %d, size: %u @%p\n",
       offset, offset_label, size, addr);

  if (!IsTraceStreamEnabled())
    return;

  pipe_msg msg = {
    .msg_type = add_constraint_type,
    .flags = 0,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .label = offset_label, // just in case
    .result = (uint64_t)offset
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }

  return;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_add_constraint(dfsan_label label, uint8_t result) {
  if (label == 0)
    return;

  void *addr = __builtin_return_address(0);

  AOUT("tainted add_constraint: %d, result: %u @%p\n", label, result, addr);

  if (!IsTraceStreamEnabled())
    return;

  pipe_msg msg = {
    .msg_type = add_constraint_type,
    .flags = 0,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .label = label,
    .result = (uint64_t)result
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }

  return;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_minimize_label(dfsan_label label, u64 size, dfsan_label bounds) {
  if (label == 0 || label == kInitializingLabel)
    return;

  void *addr = __builtin_return_address(0);

  AOUT("minimize label: %d, bounds: %d, size: %lu\n", label, bounds, size);

  if (bounds != 0) {
    dfsan_label_info *bounds_info = get_label_info(bounds);
    if (bounds_info->op == __dfsan::Alloca) {
      AOUT("update size label from %d to %d\n", bounds_info->l2, label);
      bounds_info->l2 = label;
    }
  }

  if (!IsTraceStreamEnabled())
    return;

  pipe_msg msg = {
    .msg_type = minimize_type,
    .flags = 0,
    .instance_id = __instance_id,
    .addr = 0,
    .context = __taint_trace_callstack,
    .label = label,
    .result = 0
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }

  if (!flags().allow_zero_size_alloc && size == 0) {
    // Emit this after the minimize message so the manager records the hint
    // before solving the synthetic nonzero condition.
    static constexpr uint32_t kMinimizeNonzeroCid = 12;
    dfsan_label_info *size_info = get_label_info(label);
    dfsan_label nonzero_label =
        dfsan_union(label, 0, (__dfsan::bvneq << 8) | ICmp, size_info->size, 0, 0);
    __taint_send_cond(nonzero_label, 0, 1, 0, kMinimizeNonzeroCid, addr);
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_memcmp(dfsan_label label) {
  if (label == 0)
    return;

  void *addr = __builtin_return_address(0);

  if (label == kInitializingLabel) {
    // uninitialized label
    AOUT("WARNING: uninitialized label %u @%p\n", label, addr);
    if (flags().solve_ub) __send_ubi(label, 0, 0, addr);
    if (flags().exit_on_memerror) Die();
    else return;
  }

  dfsan_label_info *info = get_label_info(label);

  AOUT("tainted memcmp: %d, size: %d\n", label, info->size);

  if (!IsTraceStreamEnabled())
    return;

  uint16_t has_content = 1;
  // If fmemcmp materialized a constant operand, its op value no longer holds
  // an address. Solver-side trailers can carry the saved bytes only when the
  // complete comparison fits in the two-word representation.
  if (is_fmemcmp(info->op)) {
    bool concrete_op2 = info->l1 == CONST_LABEL &&
                        fmemcmp_operand_captured(info->op, false);
    bool concrete_op1 = info->l2 == CONST_LABEL &&
                        fmemcmp_operand_captured(info->op, true);
    has_content = info->size != 0 && info->size <= 16 &&
                  (concrete_op1 || concrete_op2);
  } else if ((info->l1 != CONST_LABEL && info->l2 != CONST_LABEL) ||
             info->size == 0) {
    has_content = 0;
  }

  pipe_msg msg = {
    .msg_type = memcmp_type,
    .flags = has_content,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .label = label, // just in case
    .result = (uint64_t)info->size
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }

  if (!has_content)
    return;

  size_t msg_size = sizeof(memcmp_msg) + info->size;
  memcmp_msg *mmsg = (memcmp_msg*)__builtin_alloca(msg_size);
  mmsg->label = label;
  if (is_fmemcmp(info->op)) {
    bool use_op1 = info->l1 == CONST_LABEL;
    uint64_t concrete_bytes = use_op1 ? info->op1.i : info->op2.i;
    uint64_t concrete_bytes_hi = use_op1 ? info->op1_hi : info->op2_hi;
    internal_memcpy(mmsg->content, &concrete_bytes,
                    info->size > 8 ? 8 : info->size);
    if (info->size > 8)
      internal_memcpy(mmsg->content + 8, &concrete_bytes_hi,
                      info->size - 8);
  } else {
    // Copy concrete content: use op1 if l1 is concrete, else op2.
    void *concrete_ptr = (info->l1 == CONST_LABEL)
                             ? (void *)info->op1.i : (void *)info->op2.i;
    internal_memcpy(mmsg->content, concrete_ptr, info->size);
  }
  AOUT("sending memcmp content for label %d, size %u, msg_size=%lu\n", label, info->size, msg_size);

  // FIXME: assuming single writer so msg will arrive in the same order
  if (internal_write(__pipe_fd, mmsg, msg_size) < 0) {
    Die();
  }

  return;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_trace_memerr(dfsan_label ptr_label, uptr ptr, dfsan_label size_label,
                     uint64_t size, uint16_t flag, void *addr) {
  if (ptr_label == 0 && size_label == 0)
    return;

  if (!IsTraceStreamEnabled())
    return;

  uint64_t r = 0;
  switch(flag) {
    case F_MEMERR_UAF: r = ptr; break;
    case F_MEMERR_OLB: r = ptr; break;
    case F_MEMERR_OUB: r = ptr + size; break;
    case F_MEMERR_UBI: r = ptr; break;
    default: return;
  }

  pipe_msg msg = {
    .msg_type = memerr_type,
    .flags = flag,
    .instance_id = __instance_id,
    .addr = (uptr)addr,
    .context = __taint_trace_callstack,
    .label = ptr_label, // just in case
    .result = r
  };

  if (internal_write(__pipe_fd, &msg, sizeof(msg)) < 0) {
    Die();
  }
}

extern "C" void InitializeSymSanSolver() {
  __instance_id = flags().instance_id;
  __session_id = flags().session_id;
  __pipe_fd = flags().pipe_fd;
  __control_pipe_fd = flags().control_pipe_fd;
  InitializeSinglePassCapture();
}
