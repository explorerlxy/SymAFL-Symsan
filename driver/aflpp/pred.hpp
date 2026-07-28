// Self-contained branch predicates for SymAFL v2 PCBT screening.
//
// RunConverter converts the SymSan union-table ASTs of ONE traced run into
// a single shared PredArena (post-order PNode array, one conversion per
// union-table label — the table is hash-consed, so sharing is maximal).
// A Predicate is (arena, root index) — cheap to store per tree node, no
// per-predicate copies of shared subexpressions.
//
// Integer bit-vector ops only; FP/string/gep subtrees are marked opaque —
// screening treats an opaque node as "cannot decide -> admit".
//
// eval_predicate() interprets a predicate against a concrete input with
// SMT-LIB bit-vector corner semantics (div-by-zero rules, shift>=width,
// exact-width masking).
#pragma once

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <vector>

#include "dfsan/dfsan.h"

namespace pcbt {

enum class PKind : uint8_t {
  Opaque = 0,
  Read,   // input bytes: value=byte offset, aux=nbytes (little-endian)
  Const,  // value=constant (masked to bits)
  Add, Sub, Mul, UDiv, SDiv, URem, SRem, Neg,
  Not, And, Or, Xor, Shl, LShr, AShr,
  Equal, Distinct, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,
  ZExt, SExt, Extract, Concat,
};

struct PNode {
  PKind kind;
  uint16_t bits;       // result width in bits; for comparisons: operand width
  uint32_t a;          // left/only child index (UINT32_MAX = none)
  uint32_t b;          // right child index (UINT32_MAX = none)
  uint64_t value;      // Const: value; Read: byte offset; Extract: bit offset
  uint32_t aux;        // Read: nbytes
};

struct PredArena {
  std::vector<PNode> nodes;  // post-order by label (children before parents)
};
using ArenaPtr = std::shared_ptr<PredArena>;

struct Predicate {
  ArenaPtr arena;
  uint32_t root = 0;
  bool opaque = false;
  // subtree indices in ascending arena order (children precede parents):
  // the evaluation order for this predicate
  std::vector<uint32_t> order;
  // input-read set of this predicate: sorted unique (offset, nbytes) pairs
  std::vector<std::pair<uint32_t, uint32_t>> reads;

  bool reads_range(uint32_t lo, uint32_t hi) const {
    for (auto &r : reads) {
      uint32_t rlo = r.first, rhi = r.first + r.second - 1;
      if (rlo <= hi && lo <= rhi) return true;
    }
    return false;
  }
};

// Converts the union-table ASTs of one traced run into one shared arena.
// Create once per traced run; call conv() per branch label (memoized
// across calls). Labels are topologically ordered (child < parent), so
// each label is converted at most once per run.
class RunConverter {
 public:
  RunConverter(const dfsan_label_info *table, size_t table_labels);
  // Convert the subtree at `label`; returns a Predicate view into the
  // shared arena (possibly marked opaque).
  Predicate conv(uint32_t label);
  ArenaPtr arena() const { return arena_; }

 private:
  const dfsan_label_info *table_;
  size_t table_labels_;
  ArenaPtr arena_;
  std::unordered_map<uint32_t, uint32_t> label_map_;  // label -> arena index
  bool overflow_ = false;

  uint32_t convert(uint32_t label, size_t depth);
  uint32_t convert_op(const dfsan_label_info *info, uint32_t op,
                      uint32_t op_lo, size_t depth);
  uint32_t add(PKind kind, uint16_t bits, uint32_t a, uint32_t b,
               uint64_t value = 0, uint32_t aux = 0);
  uint32_t add_const(uint64_t value, uint16_t bits);
  uint32_t conv_child(uint32_t label, uint64_t cval, uint16_t cbits,
                      size_t depth);
  void collect_reads(uint32_t root, Predicate &pred);
};

// Evaluate a predicate against a concrete input. Returns false on undefined
// evaluation (read past input end); on success returns true and sets *out
// to the root value (0/1 for comparison roots).
bool eval_predicate(const Predicate &pred, const uint8_t *input, uint32_t len,
                    uint64_t *out);

}  // namespace pcbt
