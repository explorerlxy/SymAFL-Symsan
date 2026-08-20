// RUN: env KO_USE_SYMSAN_ONLY=1 KO_USE_NATIVE_LIBCXX=1 \
// RUN:   %ko-clangxx -I%S/../runtime -O0 -fno-builtin-memcmp -o %t.fmemcmp %s
// RUN: %t.fmemcmp | FileCheck %s

// Regression for tagged fmemcmp operand capture in __taint_union / __dfsw_memcmp.
// Requires KO_USE_SYMSAN_ONLY=1 so the binary links libsymsan_rt-x86_64.a, which
// contains the strong __taint_union with IsAccessibleMemoryRange capture.

#include "dfsan/dfsan.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <sys/mman.h>
#include <unistd.h>

static int failures = 0;

#define CHECK(cond, msg)                                                       \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL: %s (%s:%d)\n", msg, __FILE__, __LINE__);          \
      failures++;                                                              \
    }                                                                          \
  } while (0)

int main() {
  // --- Setup symbolic input buffer ---
  uint8_t input[4] = {0x10, 0x20, 0x30, 0x40};
  dfsan_label input_label = dfsan_create_label(1, 0, 4);
  dfsan_set_label(input_label, input, sizeof(input));

  // --- Test 1: memcmp(symbolic, static_constant) ---
  {
    static const uint8_t magic[4] = {0x11, 0x22, 0x33, 0x44};
    int result = memcmp(input, magic, 4);
    dfsan_label ret_label = dfsan_get_label(&result);
    CHECK(ret_label != 0, "memcmp(sym,const) should have taint label");

    dfsan_label_info *info = dfsan_get_label_info(ret_label);
    // fmemcmp base op must match; capture flags in high bits
    CHECK((info->op & 0xff) == __dfsan::fmemcmp,
          "base op should be fmemcmp");
    CHECK(info->size == 4, "fmemcmp size should be 4 bytes");

    // Both operands are readable -> both capture bits set
    CHECK(__dfsan::fmemcmp_operand_captured(info->op, false),
          "operand1 captured flag set");
    CHECK(__dfsan::fmemcmp_operand_captured(info->op, true),
          "operand2 captured flag set");

    // After commutative normalization the constant should be on op1 as
    // packed LE bytes.  The symbolic input bytes are on op2.
    // 0x11 0x22 0x33 0x44 => 0x44332211
    CHECK(info->op1.i == 0x44332211ULL,
          "op1 should be packed magic bytes");

    printf("PASS: memcmp(symbolic, static_constant)\n");
  }

  // --- Test 2: memcmp(static_constant, symbolic) ---
  {
    static const uint8_t magic[4] = {0xAA, 0xBB, 0xCC, 0xDD};
    int result = memcmp(magic, input, 4);
    dfsan_label ret_label = dfsan_get_label(&result);
    CHECK(ret_label != 0, "memcmp(const,sym) should have taint label");

    dfsan_label_info *info = dfsan_get_label_info(ret_label);
    CHECK((info->op & 0xff) == __dfsan::fmemcmp,
          "base op should be fmemcmp (const,sym)");
    CHECK(info->size == 4, "fmemcmp size should be 4 bytes (const,sym)");
    CHECK(__dfsan::fmemcmp_operand_captured(info->op, false),
          "operand1 captured (const,sym)");
    CHECK(__dfsan::fmemcmp_operand_captured(info->op, true),
          "operand2 captured (const,sym)");
    // After commutative normalization the constant moves to op1:
    // 0xAA 0xBB 0xCC 0xDD => 0xDDCCBBAA
    CHECK(info->op1.i == 0xDDCCBBAAULL,
          "op1 should be packed magic bytes (const,sym)");

    printf("PASS: memcmp(static_constant, symbolic)\n");
  }

  // --- Test 3: unreadable operand via direct dfsan_union ---
  // Do NOT use memcmp / __dfsw_memcmp with an invalid pointer: the wrapper
  // calls libc memcmp first, which would crash.  Test the capture helper
  // directly.
  {
    long page_size = sysconf(_SC_PAGESIZE);
    void *bad_page = mmap(nullptr, (size_t)page_size, PROT_NONE,
                          MAP_PRIVATE | MAP_ANON, -1, 0);
    CHECK(bad_page != MAP_FAILED, "mmap PROT_NONE should succeed");

    dfsan_label result = dfsan_union(
        0, input_label, __dfsan::fmemcmp, 4,
        reinterpret_cast<uint64_t>(bad_page),
        reinterpret_cast<uint64_t>(input));

    CHECK(result != 0, "dfsan_union with bad operand should return label");

    dfsan_label_info *info = dfsan_get_label_info(result);
    CHECK((info->op & 0xff) == __dfsan::fmemcmp,
          "base op should be fmemcmp (bad operand)");

    // Unreadable side: capture flag clear, op value unchanged (still address)
    // Which side is l1/l2 depends on commutative normalization, so test both.
    bool op1_unreadable = (info->l1 == 0 && !__dfsan::fmemcmp_operand_captured(info->op, false));
    bool op2_unreadable = (info->l2 == 0 && !__dfsan::fmemcmp_operand_captured(info->op, true));
    bool one_unreadable = (op1_unreadable && info->l2 != 0 &&
                           __dfsan::fmemcmp_operand_captured(info->op, true)) ||
                          (op2_unreadable && info->l1 != 0 &&
                           __dfsan::fmemcmp_operand_captured(info->op, false));
    CHECK(one_unreadable,
          "exactly one operand should be unreadable with address preserved");

    printf("PASS: direct dfsan_union with unreadable operand survived\n");
    munmap(bad_page, (size_t)page_size);
  }

  // --- Test 4: NULL operand via direct dfsan_union ---
  {
    dfsan_label result = dfsan_union(
        input_label, 0, __dfsan::fmemcmp, 4,
        reinterpret_cast<uint64_t>(input), 0ULL);
    CHECK(result != 0, "dfsan_union with null constant should return label");

    dfsan_label_info *info = dfsan_get_label_info(result);
    CHECK((info->op & 0xff) == __dfsan::fmemcmp,
          "base op should be fmemcmp (null operand)");
    // Null address: IsAccessibleMemoryRange probe fails, capture bit stays
    // clear and the value remains zero.
    bool null_uncaptured = (info->l1 == 0 && !__dfsan::fmemcmp_operand_captured(info->op, false) &&
                            info->op1.i == 0ULL) ||
                           (info->l2 == 0 && !__dfsan::fmemcmp_operand_captured(info->op, true) &&
                            info->op2.i == 0ULL);
    CHECK(null_uncaptured,
          "null constant operand should be uncaptured with zero value");

    printf("PASS: direct dfsan_union with null operand survived\n");
  }

  // A bswap-style Extract outside the represented shadow width is concrete,
  // not a symbolic byte. The runtime must drop that label rather than emit an
  // out-of-range Extract node for the SEDBT converter.
  {
    dfsan_label result = dfsan_union(
        input_label, 0, __dfsan::Extract, 8, 0, sizeof(input) * 8);
    CHECK(result == 0, "out-of-range Extract should be clean");
    printf("PASS: out-of-range Extract remains clean\n");
  }

  if (failures) {
    fprintf(stderr, "%d test(s) FAILED\n", failures);
    return 1;
  }
  // CHECK: PASS: memcmp(symbolic, static_constant)
  // CHECK: PASS: memcmp(static_constant, symbolic)
  // CHECK: PASS: direct dfsan_union with unreadable operand survived
  // CHECK: PASS: direct dfsan_union with null operand survived
  // CHECK: PASS: out-of-range Extract remains clean
  printf("ALL PASS\n");
  return 0;
}
