// RUN: env KO_USE_SYMSAN_ONLY=1 KO_USE_FASTGEN=1 %ko-clangxx -I%S/../runtime -I/usr/lib/llvm-18/include -O0 -o %t.sret %s
// RUN: %t.sret | FileCheck %s

#include "dfsan/dfsan.h"

#include <stdint.h>
#include <stdio.h>

typedef struct {
  uint64_t a;
  uint64_t b;
  uint64_t c;
} triple;

triple __attribute__((noinline)) make_triple(uint64_t x) {
  triple value = {x, x + 1, x + 2};
  return value;
}

int __attribute__((noinline)) consume_triple(triple value) {
  dfsan_label field_label = dfsan_get_label(&value.b);
  if (field_label == 0) {
    puts("FAIL: byval aggregate shadow was lost");
    return 1;
  }
  puts("PASS: byval aggregate shadow preserved");
  return value.b == 7 ? 0 : 1;
}

int main() {
  uint64_t x = 6;
  dfsan_label input_label = dfsan_create_label(1, 0, sizeof(x));
  dfsan_set_label(input_label, &x, sizeof(x));
  return consume_triple(make_triple(x));
}

// CHECK: PASS: byval aggregate shadow preserved
