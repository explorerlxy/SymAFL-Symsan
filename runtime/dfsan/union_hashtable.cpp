#include "sanitizer_common/sanitizer_libc.h"
#include "union_hashtable.h"
#include "union_util.h"

using namespace __taint;

union_hashtable::union_hashtable(uint64_t n) {
  bucket_size = n;
  bucket = reinterpret_cast<atomic_uintptr_t*>(
      allocator_alloc(n * sizeof(atomic_uintptr_t)));
  // No zeroing needed: the bucket region comes from the no-reserve,
  // demand-zero allocator mapping, so it is already zero. The former 8 MB
  // memset was redundant work AND ran once per forkserver child: this global
  // constructor's default init priority (65535) runs AFTER the AFL forkserver
  // starts (afl_init_shim is constructor(101)), so every forked child
  // re-executed it, touching ~2000 fresh pages (~1.3 ms/run). Removing it
  // raised the concolic admit rate 310 -> 529/s (A/B, 60s XZ, 2026-08-05).
}

uint32_t
union_hashtable::hash(const dfsan_label_info &key) {
  return key.hash & (bucket_size - 1);
}

void
union_hashtable::insert(dfsan_label_info *key, dfsan_label entry) {
  uint32_t index = hash(*key);
  auto curr = (struct union_hashtable_entry *)
      allocator_alloc(sizeof(struct union_hashtable_entry));
  curr->key = key; curr->entry = entry;
  uptr p = atomic_load(&bucket[index], memory_order_acquire);
  while (true) {
    curr->next = reinterpret_cast<struct union_hashtable_entry *>(p);
    if (atomic_compare_exchange_strong(&bucket[index], &p, (uptr)curr,
                                       memory_order_seq_cst))
      break; // spin until succeed, when fail, p will contain the current head
  }
}

option
union_hashtable::lookup(const dfsan_label_info &key) {
  uint64_t index = hash(key);
  uptr p = atomic_load(&bucket[index], memory_order_acquire);
  auto curr = reinterpret_cast<struct union_hashtable_entry *>(p);
  while (curr) {
    if (*(curr->key) == key) {
      return some_dfsan_label(curr->entry);
    }
    curr = curr->next; // no data race here
  }
  return none();
}
