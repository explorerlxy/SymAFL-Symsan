// Self-contained branch predicates for SymAFL v2 PCBT screening.
//
// Tree owns one PredArena for its lifetime. RunConverter converts one traced
// run into that shared post-order PNode array and memoizes only that run's
// union-table labels. A Predicate is a root index into the tree arena, so
// nodes do not retain a per-trace shared_ptr or duplicate expression views.
//
// The PCBT condition grammar is the scalar integer bit-vector subset emitted
// by the target preflight.  Conversion is iterative and total for that
// grammar; a condition outside it is rejected by preflight rather than given
// an invented branch result.
//
// eval_predicate() interprets a predicate against a concrete input with
// SMT-LIB bit-vector corner semantics (div-by-zero rules, shift>=width,
// exact-width masking).
#pragma once

#include <cstdint>
#include <cstddef>
#include <string>
#include <unordered_map>
#include <vector>

#include "dfsan/dfsan.h"

namespace pcbt {

enum class PKind : uint8_t {
  Opaque = 0,
  Read,   // input bytes: value=byte offset, nbytes=bits/8 (little-endian)
  Const,  // value=constant (masked to bits)
  Add, Sub, Mul, UDiv, SDiv, URem, SRem, Neg,
  Not, And, Or, Xor, Shl, LShr, AShr,
  Equal, Distinct, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge,
  ZExt, SExt, Extract, Concat, Memcmp,
};

// A conversion failure is never a predicate result.  It is retained as
// aggregate telemetry so supported-condition coverage can be audited without
// inflating every PCBT node.
enum class PredError : uint8_t {
  None = 0,
  InvalidRoot,
  InvalidLabel,
  InitializingLabel,
  InvalidWidth,
  DepthLimit,
  BadLoad,
  BadConcat,
  UnsupportedOp,
  UnsupportedCompare,
  UncapturedMemcmpOperand,
  ArenaLimit,
  NodeLimit,
  Count,
};

constexpr size_t kPredErrorCount = static_cast<size_t>(PredError::Count);
const char *pred_error_name(PredError error);

struct PNode {
  uint64_t value;      // Const: value; Read: byte offset; Extract: bit offset
  uint32_t a;          // left/only child index (UINT32_MAX = none)
  uint32_t b;          // right child index (UINT32_MAX = none)
  uint8_t bits;        // result width in bits; for comparisons: operand width
  PKind kind;
};

struct PredArena {
  std::vector<PNode> nodes;  // post-order by label (children before parents)
};

// One byte of a string content label expanded for the scalar interpreter.
struct StringByte {
  uint32_t node;    // arena node evaluating this byte (PKind::Read)
  uint32_t offset;  // input byte offset this Read samples
};

struct Predicate {
  uint32_t root = 0;
  bool opaque = false;
  PredError error = PredError::None;
  uint16_t error_op = 0;
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

// Converts one traced run into the Tree-owned arena. Create once per trace;
// call conv() per branch label. A failed root conversion does not make later
// labels opaque.
class RunConverter {
 public:
  RunConverter(const dfsan_label_info *table, size_t table_labels,
               PredArena *arena);
  // Convert the subtree at `label`; returns a Predicate view into the
  // shared arena (possibly marked opaque).
  Predicate conv(uint32_t label);
 private:
  const dfsan_label_info *table_;
  size_t table_labels_;
  PredArena *arena_;
  size_t predicate_start_ = 0;
  std::unordered_map<uint32_t, uint32_t> label_map_;  // label -> arena index
  std::vector<uint32_t> inserted_labels_;
  PredError error_ = PredError::None;
  uint16_t error_op_ = 0;

  uint32_t convert(uint32_t label);
  uint32_t convert_op(const dfsan_label_info *info, uint32_t op,
                      uint32_t op_lo);
  uint32_t add(PKind kind, uint16_t bits, uint32_t a, uint32_t b,
               uint64_t value = 0);
  uint32_t add_const(uint64_t value, uint16_t bits);
  uint32_t conv_child(uint32_t label, uint64_t cval, uint16_t cbits);
  uint8_t child_count(const dfsan_label_info *info, uint32_t op,
                      uint32_t op_lo) const;
  void fail(PredError error, uint16_t op = 0);

  // String/FP byte-level lowering (goal 2). These expand a string-op label or
  // an FP comparison into scalar bit-vector nodes, keeping the predicate
  // input-dependent (never using the label's concrete op1/op2 as a constant).
  bool string_bytes(dfsan_label content, size_t max_bytes,
                    std::vector<StringByte> &out);
  bool collect_byte_offsets(dfsan_label label, size_t cap,
                            std::vector<uint64_t> &offs);
  uint32_t convert_strlen_cmp(const dfsan_label_info *info, uint32_t op,
                              const dfsan_label_info &strlen_info);
  uint32_t convert_strchr_cmp(const dfsan_label_info *info, uint32_t op,
                              const dfsan_label_info &chr_info);
  uint32_t convert_strstr_cmp(const dfsan_label_info *info, uint32_t op,
                              const dfsan_label_info &strstr_info);
  uint32_t convert_fcmp(const dfsan_label_info *info, uint32_t op);
  uint32_t fp_is_nan(uint32_t a, uint16_t w);
  uint32_t fp_is_zero(uint32_t a, uint16_t w);
  uint32_t fp_total_order(uint32_t a, uint16_t w);
};

// A context shares values across root evaluations for one candidate.  PCBT
// paths created from a single trace share PNodes, so this avoids re-evaluating
// their common expression DAG at every depth.
class EvalContext {
 public:
  void Reset();

 private:
  // Flat value cache addressed by arena node index: stamps_[i] == generation_
  // marks values_[i] valid for the current candidate input.  Reset() advances
  // the generation so a slot surviving from an earlier input or from a
  // rolled-back arena region is never read as valid.
  std::vector<uint64_t> values_;
  std::vector<uint32_t> stamps_;
  uint32_t generation_ = 1;
  std::vector<std::pair<uint32_t, bool>> stack_;
  friend bool eval_predicate(const PredArena &, const Predicate &,
                             const uint8_t *, uint32_t, uint64_t *,
                             EvalContext *);
};

// Evaluate only the root-reachable DAG against a concrete input. Returns false
// on undefined evaluation (read past input end); on success sets *out to the
// root value (0/1 for comparison roots). Passing a context retains values from
// earlier roots for the same input; callers must Reset() it for a new input.
bool eval_predicate(const PredArena &arena, const Predicate &pred,
                    const uint8_t *input, uint32_t len, uint64_t *out,
                    EvalContext *context = nullptr);

}  // namespace pcbt
