// Self-contained branch predicate for SymAFL v2 PCBT screening.
//
// predicate_from_label() converts a SymSan union-table AST (rooted at a
// 32-bit label) into a compact post-order node array with INLINE constants
// (no input_args indirection, no parser involvement). Integer bit-vector
// ops only; FP/string/gep subtrees are marked opaque — screening treats an
// opaque node as "cannot decide -> admit" (conservative).
//
// eval_predicate() interprets a predicate against a concrete input with
// SMT-LIB bit-vector corner semantics (div-by-zero rules, shift>=width,
// exact-width masking), the reference for the future JIT tier.
#pragma once

#include <cstdint>
#include <memory>
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

struct Predicate {
  std::vector<PNode> nodes;  // post-order; root = nodes.back()
  bool opaque = false;
};

using PredicatePtr = std::shared_ptr<Predicate>;

// Convert the union-table AST rooted at `label` into a Predicate.
// `table`/`table_labels` describe the launcher's shared union table, whose
// content is valid for the current traced run only. Returns a predicate
// (possibly marked opaque) or nullptr on structural failure.
PredicatePtr predicate_from_label(const dfsan_label_info *table,
                                  size_t table_labels, uint32_t label);

// Evaluate against a concrete input. Returns false on undefined evaluation
// (read past input end, opaque node); on success returns true and sets
// *out to the root value (0/1 for comparison roots).
bool eval_predicate(const Predicate &pred, const uint8_t *input, uint32_t len,
                    uint64_t *out);

}  // namespace pcbt
