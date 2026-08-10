// RUN: env KO_USE_FASTGEN=1 KO_USE_NATIVE_LIBCXX=1 KO_CXX=clang++-18 \
// RUN:   %ko-clangxx -I%S/../runtime -I/usr/lib/llvm-18/include -O0 \
// RUN:   -o %t.extract %s
// RUN: %t.extract | FileCheck %s

#include "dfsan/dfsan.h"

#include <cassert>
#include <cstdint>
#include <cstdio>

int main() {
  dfsan_label parent = dfsan_create_label(1, 0, 4);
  dfsan_label in_range = dfsan_union(
      parent, 0, __dfsan::Extract, 8, 0, 24);
  dfsan_label out_of_range = dfsan_union(
      parent, 0, __dfsan::Extract, 8, 0, 32);
  assert(in_range != 0);
  assert(out_of_range == 0);
  std::puts("PASS: runtime drops out-of-range Extract");
  return 0;
}

// CHECK: PASS: runtime drops out-of-range Extract
