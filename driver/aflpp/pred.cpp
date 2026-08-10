#include "pred.hpp"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <string>
#include <unordered_map>
#include <unordered_set>

using namespace __dfsan;

namespace pcbt {

namespace {
constexpr uint32_t kNoChild = UINT32_MAX;
constexpr uint32_t kInvalidNode = UINT32_MAX;
constexpr size_t kMaxPredicateNodes = 2'000'000;
// Byte-level expansion caps for string-op lowering (goal 2).  Exceeding the
// cap marks the predicate opaque (conservative admission) rather than blowing
// the shared arena budget.
constexpr size_t kMaxStrlenBytes = 256;
constexpr size_t kMaxSearchBytes = 512;

// Length-boundary count ops (flen_count family). They share the Count-family
// node lowering; flen_eof and fsize are handled separately.
static inline bool is_flen_count_op(uint16_t op_lo) {
  return op_lo == __dfsan::flen_count || op_lo == __dfsan::flen_count_neg1 ||
         op_lo == __dfsan::flen_count_elems;
}

// A symbolic operand may itself be derived from the flen label being lowered.
// Reusing that operand as the Count clamp would create x < min(x, ...), which
// is not the original comparison semantics. Keep the recorded request clamp
// for this dependency case; splice only independent symbolic requests.
static bool label_depends_on(const dfsan_label_info *table, size_t labels,
                             uint32_t root, uint32_t target) {
  if (root == 0 || target == 0 || root >= labels || target >= labels)
    return false;
  std::vector<uint32_t> stack = {root};
  std::unordered_set<uint32_t> seen;
  while (!stack.empty()) {
    uint32_t label = stack.back();
    stack.pop_back();
    if (label == target) return true;
    if (!seen.insert(label).second || label >= labels) continue;
    const dfsan_label_info &info = table[label];
    if (info.l1 != 0 && info.l1 < labels) stack.push_back(info.l1);
    if (info.l2 != 0 && info.l2 < labels) stack.push_back(info.l2);
  }
  return false;
}

struct ConvertFrame {
  uint32_t label;
  bool expanded;
};
}  // namespace

void EvalContext::Reset() {
  stack_.clear();
  if (++generation_ == 0) {
    std::fill(stamps_.begin(), stamps_.end(), 0);
    generation_ = 1;
  }
}

const char *pred_error_name(PredError error) {
  switch (error) {
    case PredError::None: return "none";
    case PredError::InvalidRoot: return "invalid_root";
    case PredError::InvalidLabel: return "invalid_label";
    case PredError::InitializingLabel: return "initializing_label";
    case PredError::InvalidWidth: return "invalid_width";
    case PredError::DepthLimit: return "depth_limit";
    case PredError::BadLoad: return "bad_load";
    case PredError::BadConcat: return "bad_concat";
    case PredError::UnsupportedOp: return "unsupported_op";
    case PredError::UnsupportedCompare: return "unsupported_compare";
    case PredError::UncapturedMemcmpOperand: return "uncaptured_memcmp_operand";
    case PredError::ArenaLimit: return "arena_limit";
    case PredError::NodeLimit: return "node_limit";
    case PredError::Count: break;
  }
  return "unknown";
}

RunConverter::RunConverter(const dfsan_label_info *table, size_t table_labels,
                           PredArena *arena)
    : table_(table), table_labels_(table_labels), arena_(arena) {}

void RunConverter::fail(PredError error, uint16_t op) {
  if (error_ == PredError::None) {
    error_ = error;
    error_op_ = op;
  }
}

uint32_t RunConverter::add(PKind kind, uint16_t bits, uint32_t a, uint32_t b,
                           uint64_t value) {
  if (bits == 0 || bits > 64 ||
      arena_->nodes.size() - predicate_start_ >= kMaxPredicateNodes ||
      arena_->nodes.size() >= kInvalidNode) {
    if (bits == 0 || bits > 64) {
      fail(PredError::InvalidWidth, op_context_);
    } else if (arena_->nodes.size() - predicate_start_ >= kMaxPredicateNodes) {
      fail(PredError::ArenaLimit);
    } else {
      fail(PredError::NodeLimit);
    }
    return kInvalidNode;
  }
  arena_->nodes.push_back({value, a, b, (uint8_t)bits, kind});
  return (uint32_t)arena_->nodes.size() - 1;
}

uint32_t RunConverter::add_const(uint64_t value, uint16_t bits) {
  return add(PKind::Const, bits, kNoChild, kNoChild, value);
}

uint32_t RunConverter::conv_child(uint32_t label, uint64_t cval,
                                  uint16_t cbits) {
  if (label == 0) return add_const(cval, cbits);
  auto it = label_map_.find(label);
  if (it == label_map_.end()) {
    fail(PredError::InvalidLabel);
    return kInvalidNode;
  }
  return it->second;
}

uint8_t RunConverter::child_count(const dfsan_label_info *info, uint32_t op,
                                  uint32_t op_lo) const {
  if (op == 0 || op_lo == Load) return 0;
  if (op_lo == PtrToInt) return 1;
  if (op == __dfsan::Extract || op_lo == Trunc ||
      op_lo == Neg || op_lo == Not || op_lo == ZExt || op_lo == SExt ||
      op_lo == __dfsan::ctlz || op_lo == __dfsan::cttz ||
      op_lo == __dfsan::fp_neg || op_lo == __dfsan::fp_fabs ||
      op_lo == __dfsan::fp_sqrt || op_lo == __dfsan::fp_round ||
      op_lo == __dfsan::fp_is_nan || op_lo == __dfsan::fp_is_inf ||
      op_lo == __dfsan::fp_is_finite || op_lo == __dfsan::fp_signbit ||
      op_lo == __dfsan::fp_lrint || op_lo == __dfsan::fp_exp ||
      op_lo == __dfsan::fp_exp2 || op_lo == __dfsan::fp_log ||
      op_lo == __dfsan::fp_log2 || op_lo == __dfsan::fp_log10 ||
      op_lo == __dfsan::fp_log1p || op_lo == FPTrunc || op_lo == FPExt ||
      op_lo == FPToUI || op_lo == FPToSI || op_lo == UIToFP ||
      op_lo == SIToFP)
    return 1;
  if (op == __dfsan::Concat || is_fmemcmp(op) || op_lo == ICmp ||
      op_lo == FCmp || op_lo == Add || op_lo == Sub || op_lo == Mul ||
      op_lo == UDiv || op_lo == SDiv || op_lo == URem || op_lo == SRem ||
      op_lo == __dfsan::umin || op_lo == __dfsan::umax ||
      op_lo == __dfsan::smin || op_lo == __dfsan::smax ||
      op_lo == Shl || op_lo == LShr || op_lo == AShr || op_lo == And ||
      op_lo == Or || op_lo == Xor || op_lo == FAdd || op_lo == FSub ||
      op_lo == FMul || op_lo == FDiv || op_lo == FRem ||
      op_lo == __dfsan::fp_min || op_lo == __dfsan::fp_max ||
      op_lo == __dfsan::fp_copysign || op_lo == __dfsan::fp_pow)
    return 2;
  if (op == __dfsan::fsize || op == __dfsan::flen_eof ||
      op == __dfsan::flen_count || op == __dfsan::flen_count_neg1 ||
      op == __dfsan::flen_count_elems)
    return 0;
  return 0;
}

uint32_t RunConverter::convert(uint32_t label) {
  if (label >= table_labels_) {
    fail(PredError::InvalidLabel);
    return kInvalidNode;
  }
  if (label == kInitializingLabel) {
    fail(PredError::InitializingLabel);
    return kInvalidNode;
  }
  auto it = label_map_.find(label);
  if (it != label_map_.end()) return it->second;

  const size_t nodes_checkpoint = arena_->nodes.size();
  const size_t labels_checkpoint = inserted_labels_.size();
  std::vector<ConvertFrame> stack;
  std::unordered_set<uint32_t> pending;
  stack.push_back({label, false});
  uint32_t root = kInvalidNode;

  while (!stack.empty() && error_ == PredError::None) {
    ConvertFrame frame = stack.back();
    stack.pop_back();
    if (label_map_.find(frame.label) != label_map_.end()) continue;
    if (frame.label >= table_labels_ || frame.label == kInitializingLabel) {
      fail(frame.label == kInitializingLabel ? PredError::InitializingLabel
                                             : PredError::InvalidLabel);
      break;
    }
    const dfsan_label_info *info = &table_[frame.label];
    uint32_t op = info->op;
    uint32_t op_lo = op & 0xff;
    if (!frame.expanded) {
      if (!pending.insert(frame.label).second) {
        fail(PredError::InvalidLabel);
        break;
      }
      stack.push_back({frame.label, true});
      uint8_t count = child_count(info, op, op_lo);
      // String-op vs constant comparisons (fstrlen/fstrchr/fstrstr) are
      // expanded inline into byte reads; the string-op operand is NOT a child
      // (converting it would hit UnsupportedOp and poison the whole root).
      if (op_lo == ICmp && info->l2 == 0 && info->l1 != 0 &&
          info->l1 < table_labels_) {
        uint16_t so = table_[info->l1].op & 0xff;
        if (so == __dfsan::fstrlen || so == __dfsan::fstrchr ||
            so == __dfsan::fstrrchr || so == __dfsan::fstrstr)
          count = 0;
      }
      // A wide load/concat can be immediately projected by Extract or Trunc.
      // Do not walk the unsupported wide node first; convert_op() lowers only
      // the observed scalar slice through convert_slice().
      if ((op == __dfsan::Extract || op_lo == Trunc) &&
          (info->l1 != 0 || info->l2 != 0)) {
        dfsan_label child = info->l1 != 0 ? info->l1 : info->l2;
        if (child < table_labels_ && table_[child].size > 64)
          count = 0;
      }
      if (op_lo == ICmp && info->l2 == 0 && info->l1 != 0 &&
          info->l1 < table_labels_ && is_fmemcmp(table_[info->l1].op) &&
          table_[info->l1].size > 8)
        count = 0;
      if (op_lo == Concat && info->size > 64)
        count = 0;
      if (count == 2) {
        if (info->l2 != 0) stack.push_back({info->l2, false});
        if (info->l1 != 0) stack.push_back({info->l1, false});
      } else if (count == 1) {
        // Commutative swapping in the runtime may leave a unary op's child
        // in l2 (e.g. Not after Xor-1 swap).
        if (info->l1 != 0) stack.push_back({info->l1, false});
        else if (info->l2 != 0) stack.push_back({info->l2, false});
      }
      continue;
    }

    uint32_t idx;
    if (op == 0) {
      // raw input byte: offset in op1, input id in op2 (multi-input unused)
      idx = add(PKind::Read, 8, kNoChild, kNoChild, info->op1.i);
    } else if (op_lo == Load) {
      // uload: consecutive input bytes fused into one read
      if (info->l1 == 0 || info->l1 >= table_labels_ || info->l2 == 0 ||
          info->l2 > 8 || table_[info->l1].op != 0) {
        fail(PredError::BadLoad);
        idx = kInvalidNode;
      } else {
        idx = add(PKind::Read, (uint16_t)(info->l2 * 8), kNoChild, kNoChild,
                  table_[info->l1].op1.i);
      }
    } else {
      op_context_ = static_cast<uint16_t>(op);
      idx = (op_lo == Concat && info->size > 64)
                ? convert_wide_truth(info, frame.label)
                : convert_op(info, op, op_lo);
    }
    if (idx == kInvalidNode) {
      static thread_local uint32_t forensic_reports = 0;
      if (getenv("SYMAFL_PRED_FORENSICS") && forensic_reports < 64) {
        ++forensic_reports;
        fprintf(stderr,
                "[pcbt-pred-forensic] error=%s error_op=%u root=%u "
                "root_op=%u root_size=%u root_l1=%u root_l2=%u "
                "label=%u op=%u size=%u l1=%u l2=%u op1=%llu op2=%llu\n",
                pred_error_name(error_), error_op_, root_label_,
                table_[root_label_].op, table_[root_label_].size,
                table_[root_label_].l1, table_[root_label_].l2,
                frame.label, info->op,
                info->size,
                info->l1, info->l2,
                (unsigned long long)info->op1.i,
                (unsigned long long)info->op2.i);
        for (dfsan_label child : {info->l1, info->l2}) {
          if (child != 0 && child < table_labels_)
            fprintf(stderr,
                    "[pcbt-pred-forensic] child=%u op=%u size=%u l1=%u l2=%u "
                    "op1=%llu op2=%llu\n",
                    child, table_[child].op, table_[child].size,
                    table_[child].l1, table_[child].l2,
                    (unsigned long long)table_[child].op1.i,
                    (unsigned long long)table_[child].op2.i);
        }
        uint32_t cursor = frame.label;
        for (unsigned depth = 0; depth < 8 && cursor != 0 &&
                                      cursor < table_labels_; ++depth) {
          const dfsan_label_info &trace = table_[cursor];
          uint32_t l1_op = trace.l1 != 0 && trace.l1 < table_labels_
                               ? table_[trace.l1].op : 0;
          uint32_t l2_op = trace.l2 != 0 && trace.l2 < table_labels_
                               ? table_[trace.l2].op : 0;
          fprintf(stderr,
                  "[pcbt-pred-forensic] path depth=%u label=%u op=%u size=%u "
                  "l1=%u(lop=%u) l2=%u(lop=%u)\n",
                  depth, cursor, trace.op, trace.size, trace.l1, l1_op,
                  trace.l2, l2_op);
          cursor = trace.l1 ? trace.l1 : trace.l2;
        }
      }
      break;
    }
    label_map_.emplace(frame.label, idx);
    inserted_labels_.push_back(frame.label);
    pending.erase(frame.label);
    if (frame.label == label) root = idx;
  }

  if (error_ != PredError::None || root == kInvalidNode) {
    arena_->nodes.resize(nodes_checkpoint);
    while (inserted_labels_.size() > labels_checkpoint) {
      label_map_.erase(inserted_labels_.back());
      inserted_labels_.pop_back();
    }
    return kInvalidNode;
  }
  return root;
}

uint32_t RunConverter::convert_slice(dfsan_label label, uint64_t cval,
                                     uint16_t label_bits, uint64_t offset,
                                     uint16_t width) {
  if (width == 0 || width > 64 || offset > label_bits ||
      width > static_cast<uint64_t>(label_bits) - offset) {
    if (getenv("SYMAFL_PRED_FORENSICS"))
      fprintf(stderr,
              "[pcbt-pred-slice] label=%u op=%u label_bits=%u offset=%llu "
              "width=%u cval=%llu\n",
              label, label < table_labels_ ? table_[label].op : 0,
              label_bits, (unsigned long long)offset, width,
              (unsigned long long)cval);
    fail(PredError::InvalidWidth, op_context_);
    return kInvalidNode;
  }

  if (label == 0) {
    // Concrete pieces in the runtime label grammar are at most one machine
    // word. A wider concrete-only slice would require bytes that were never
    // carried in the label table and must remain conservative.
    if (offset >= 64 || width > 64 - offset) {
      fail(PredError::InvalidWidth, op_context_);
      return kInvalidNode;
    }
    uint64_t value = cval >> offset;
    if (width < 64) value &= (uint64_t{1} << width) - 1;
    return add_const(value, width);
  }
  if (label >= table_labels_) {
    fail(PredError::InvalidLabel, op_context_);
    return kInvalidNode;
  }

  const dfsan_label_info &info = table_[label];
  uint32_t op = info.op;
  uint32_t op_lo = op & 0xff;
  if (op == 0) {
    if (offset != 0 || width != 8 || label_bits != 8) {
      fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    return add(PKind::Read, 8, kNoChild, kNoChild, info.op1.i);
  }

  if (op_lo == Load) {
    if (info.l1 == 0 || info.l1 >= table_labels_ || info.l2 == 0 ||
        info.l2 > 16 || table_[info.l1].op != 0 || (offset % 8) != 0 ||
        (width % 8) != 0 || offset + width > info.l2 * 8 || width > 64) {
      fail(PredError::BadLoad, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    return add(PKind::Read, width, kNoChild, kNoChild,
               table_[info.l1].op1.i + offset / 8);
  }

  if (op_lo == Concat) {
    if (info.l1 == 0 && info.l2 == 0) {
      fail(PredError::BadConcat, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    uint16_t low_bits = 0;
    uint16_t high_bits = 0;
    if (info.l1 != 0) {
      if (info.l1 >= table_labels_) {
        fail(PredError::InvalidLabel, static_cast<uint16_t>(op));
        return kInvalidNode;
      }
      low_bits = table_[info.l1].size;
    }
    if (info.l2 != 0) {
      if (info.l2 >= table_labels_) {
        fail(PredError::InvalidLabel, static_cast<uint16_t>(op));
        return kInvalidNode;
      }
      high_bits = table_[info.l2].size;
    }
    if (info.l1 == 0) low_bits = info.size - high_bits;
    if (info.l2 == 0) high_bits = info.size - low_bits;
    if (low_bits == 0 || high_bits == 0 ||
        static_cast<uint32_t>(low_bits) + high_bits != info.size) {
      fail(PredError::BadConcat, static_cast<uint16_t>(op));
      return kInvalidNode;
    }

    if (offset + width <= low_bits) {
      return convert_slice(info.l1, info.op1.i, low_bits, offset, width);
    }
    if (offset >= low_bits) {
      return convert_slice(info.l2, info.op2.i, high_bits,
                           offset - low_bits, width);
    }

    uint16_t low_width = static_cast<uint16_t>(low_bits - offset);
    uint16_t high_width = static_cast<uint16_t>(width - low_width);
    uint32_t low = convert_slice(info.l1, info.op1.i, low_bits,
                                 offset, low_width);
    uint32_t high = convert_slice(info.l2, info.op2.i, high_bits,
                                  0, high_width);
    if (low == kInvalidNode || high == kInvalidNode)
      return kInvalidNode;
    return add(PKind::Concat, width, low, high);
  }

  if (op == __dfsan::Extract || op_lo == Trunc || op_lo == BitCast) {
    dfsan_label child = info.l1 ? info.l1 : info.l2;
    uint64_t child_cval = info.l1 ? info.op1.i : info.op2.i;
    if (child == 0 || child >= table_labels_) {
      fail(PredError::InvalidLabel, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    uint64_t child_offset = op == __dfsan::Extract ? info.op2.i : 0;
    if (child_offset > UINT64_MAX - offset) {
      fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    if (table_[child].size <= 64) {
      // The wide projection intentionally skipped this scalar child in the
      // iterative conversion stack. Convert it as a normal subtree so its
      // arithmetic labels are materialized and memoized before the byte
      // Extract is attached.
      uint32_t child_node = convert(child);
      if (child_node == kInvalidNode) return kInvalidNode;
      if (op == __dfsan::BitCast) return child_node;
      uint64_t slice_offset = child_offset + offset;
      if (slice_offset > table_[child].size ||
          width > static_cast<uint64_t>(table_[child].size) - slice_offset) {
        if (getenv("SYMAFL_PRED_FORENSICS"))
          fprintf(stderr,
                  "[pcbt-pred-slice] scalar-extract label=%u op=%u child=%u "
                  "child_bits=%u child_offset=%llu offset=%llu width=%u\n",
                  label, op, child, table_[child].size,
                  (unsigned long long)child_offset,
                  (unsigned long long)offset, width);
        fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
        return kInvalidNode;
      }
      return add(PKind::Extract, width, child_node, kNoChild,
                 slice_offset);
    }
    return convert_slice(child, child_cval, table_[child].size,
                         child_offset + offset, width);
  }

  fail(PredError::UnsupportedOp, static_cast<uint16_t>(op));
  return kInvalidNode;
}

uint32_t RunConverter::convert_wide_truth(const dfsan_label_info *info,
                                          uint32_t label) {
  if (info == nullptr || info->size <= 64 || info->size == 0) {
    fail(PredError::InvalidWidth, info ? info->op : 0);
    return kInvalidNode;
  }

  // A bare wide label is emitted for a truthiness condition (for example a
  // pointer-sized select condition after the runtime's shadow composition).
  // Its exact branch predicate is value != 0. Project every observed byte and
  // OR their nonzero tests; never truncate the wide value to one word.
  uint32_t result = add_const(0, 8);
  for (uint64_t offset = 0; offset < info->size; offset += 8) {
    uint16_t width = static_cast<uint16_t>(
        std::min<uint64_t>(8, info->size - offset));
    uint32_t byte = convert_slice(label, 0, info->size, offset, width);
    if (byte == kInvalidNode) return kInvalidNode;
    uint32_t nonzero = add(PKind::Distinct, 8, byte, add_const(0, width));
    result = add(PKind::Or, 8, result, nonzero);
    if (result == kInvalidNode) return kInvalidNode;
  }
  return result;
}

uint32_t RunConverter::convert_op(const dfsan_label_info *info, uint32_t op,
                                  uint32_t op_lo) {
  // fmemcmp's size is a byte count, unlike ordinary label widths. Its
  // canonical -1/0/+1 result is lowered at the consuming comparison so a
  // wide operand is never truncated to the first machine word.
  if (is_fmemcmp(static_cast<uint16_t>(op))) {
    if (info->size == 0 || info->size > 16) {
      fail(PredError::InvalidWidth);
      return kInvalidNode;
    }
    // A constant fmemcmp operand starts as a target-process address. Accept it
    // only when the child runtime explicitly marked its bytes as materialized;
    // the parent must never infer bytes from an address range.
    if ((info->l1 == 0 &&
         !fmemcmp_operand_captured(info->op, false)) ||
        (info->l2 == 0 &&
         !fmemcmp_operand_captured(info->op, true))) {
      fail(PredError::UncapturedMemcmpOperand, info->op);
      return kInvalidNode;
    }
    uint16_t child_bits = static_cast<uint16_t>(info->size * 8);
    uint32_t a = conv_child(info->l1, info->op1.i, child_bits);
    uint32_t b = conv_child(info->l2, info->op2.i, child_bits);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(PKind::Memcmp, 32, a, b, info->size);
  }
  uint16_t size = info->size;
  // The local evaluator intentionally supports one machine word. Wider
  // bit-vectors must be conservatively admitted instead of being truncated.
  if (size == 0 || size > 64) {
    fail(PredError::InvalidWidth);
    return kInvalidNode;
  }

  // Pointer-to-integer conversion preserves the 64-bit pointer value. The
  // runtime child already models the absolute pointer expression, so an
  // identity conversion is both exact and sufficient for scalar PCBT.
  if (op_lo == PtrToInt) {
    uint32_t child = conv_child(info->l1 ? info->l1 : info->l2,
                                info->l1 ? info->op1.i : info->op2.i,
                                size);
    return child == kInvalidNode ? kInvalidNode : child;
  }
  PKind kind;
  bool unary = false, binary = false;

  auto fp_width = [&](uint16_t width) {
    return width == 32 || width == 64;
  };
  auto fp_child = [&](dfsan_label label, uint64_t concrete,
                      uint16_t fallback_width) {
    uint16_t child_width = fallback_width;
    if (label != 0 && label < table_labels_)
      child_width = table_[label].size;
    if (!fp_width(child_width)) {
      fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    return conv_child(label, concrete, child_width);
  };
  auto fp_operand = [&](dfsan_label label, uint64_t concrete,
                        uint16_t operand_width) {
    // A scalar FP instruction can inherit a wider shadow from a load of an
    // aggregate or a bitcasted byte span.  The runtime's little-endian label
    // grammar places the scalar operand in the low-order bits; project that
    // exact slice instead of rejecting the whole predicate or truncating a
    // prebuilt PNode.  For ordinary labels this is identical to fp_child().
    if (label != 0 && label < table_labels_ &&
        table_[label].size > operand_width) {
      if (!fp_width(operand_width)) {
        fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
        return kInvalidNode;
      }
      return convert_slice(label, concrete, table_[label].size, 0,
                           operand_width);
    }
    return fp_child(label, concrete, operand_width);
  };
  auto scalar_child = [&](dfsan_label label, uint64_t concrete,
                          uint16_t fallback_width) {
    uint16_t child_width = fallback_width;
    if (label != 0 && label < table_labels_)
      child_width = table_[label].size;
    if (child_width == 0 || child_width > 64) {
      fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    return conv_child(label, concrete, child_width);
  };

  // FP arithmetic and custom FP runtime nodes retain IEEE bit patterns in
  // their children.  Build an evaluable node instead of freezing op1/op2 or
  // rejecting the branch as opaque.
  switch (op_lo) {
    case FAdd: kind = PKind::FpAdd; binary = true; break;
    case FSub: kind = PKind::FpSub; binary = true; break;
    case FMul: kind = PKind::FpMul; binary = true; break;
    case FDiv: kind = PKind::FpDiv; binary = true; break;
    case FRem: kind = PKind::FpRem; binary = true; break;
    case __dfsan::fp_neg: kind = PKind::FpNeg; unary = true; break;
    case __dfsan::fp_fabs: kind = PKind::FpAbs; unary = true; break;
    case __dfsan::fp_sqrt: kind = PKind::FpSqrt; unary = true; break;
    case __dfsan::fp_round: kind = PKind::FpRound; unary = true; break;
    case __dfsan::fp_min: kind = PKind::FpMin; binary = true; break;
    case __dfsan::fp_max: kind = PKind::FpMax; binary = true; break;
    case __dfsan::fp_copysign: kind = PKind::FpCopySign; binary = true; break;
    case __dfsan::fp_is_nan: kind = PKind::FpIsNan; unary = true; break;
    case __dfsan::fp_is_inf: kind = PKind::FpIsInf; unary = true; break;
    case __dfsan::fp_is_finite: kind = PKind::FpIsFinite; unary = true; break;
    case __dfsan::fp_signbit: kind = PKind::FpSignBit; unary = true; break;
    case __dfsan::fp_lrint: kind = PKind::FpLrint; unary = true; break;
    case __dfsan::fp_exp: kind = PKind::FpExp; unary = true; break;
    case __dfsan::fp_exp2: kind = PKind::FpExp2; unary = true; break;
    case __dfsan::fp_log: kind = PKind::FpLog; unary = true; break;
    case __dfsan::fp_log2: kind = PKind::FpLog2; unary = true; break;
    case __dfsan::fp_log10: kind = PKind::FpLog10; unary = true; break;
    case __dfsan::fp_log1p: kind = PKind::FpLog1p; unary = true; break;
    case __dfsan::fp_pow: kind = PKind::FpPow; binary = true; break;
    case FPTrunc: kind = PKind::FpTrunc; unary = true; break;
    case FPExt: kind = PKind::FpExt; unary = true; break;
    case FPToUI: kind = PKind::FpToUI; unary = true; break;
    case FPToSI: kind = PKind::FpToSI; unary = true; break;
    case UIToFP: kind = PKind::FpToFP; unary = true; break;
    case SIToFP: kind = PKind::FpSIToFP; unary = true; break;
    default: break;
  }
  const bool is_fp_node = unary || binary &&
      (kind == PKind::FpAdd || kind == PKind::FpSub ||
       kind == PKind::FpMul || kind == PKind::FpDiv || kind == PKind::FpRem ||
       kind == PKind::FpMin || kind == PKind::FpMax ||
       kind == PKind::FpCopySign || kind == PKind::FpPow);
  if (is_fp_node && kind != PKind::FpLrint && !fp_width(size)) {
    fail(PredError::InvalidWidth, static_cast<uint16_t>(op));
    return kInvalidNode;
  }
  if (is_fp_node) {
    if (kind == PKind::FpLrint) {
      dfsan_label child = info->l1 ? info->l1 : info->l2;
      uint64_t cval = info->l1 ? info->op1.i : info->op2.i;
      uint32_t a = fp_child(child, cval, 32);
      return a == kInvalidNode ? kInvalidNode :
          add(PKind::FpLrint, 64, a, kNoChild);
    }
    if (unary) {
      dfsan_label child = info->l1 ? info->l1 : info->l2;
      uint64_t cval = info->l1 ? info->op1.i : info->op2.i;
      const bool input_is_fp =
          kind == PKind::FpTrunc || kind == PKind::FpExt ||
          kind == PKind::FpToUI || kind == PKind::FpToSI;
      uint32_t a = input_is_fp ? fp_child(child, cval, size)
                               : scalar_child(child, cval, size);
      return a == kInvalidNode ? kInvalidNode :
          add(kind, size, a, kNoChild,
              kind == PKind::FpRound ? info->op1.i : 0);
    }
    uint32_t a = fp_operand(info->l1, info->op1.i, size);
    uint32_t b = fp_operand(info->l2, info->op2.i, size);
    return a == kInvalidNode || b == kInvalidNode ? kInvalidNode :
        add(kind, size, a, b, (op >> 8) & 0xff);
  }

  switch (op_lo) {
    case Add: kind = PKind::Add; binary = true; break;
    case Sub: kind = PKind::Sub; binary = true; break;
    case Mul: kind = PKind::Mul; binary = true; break;
    case UDiv: kind = PKind::UDiv; binary = true; break;
    case SDiv: kind = PKind::SDiv; binary = true; break;
    case URem: kind = PKind::URem; binary = true; break;
    case SRem: kind = PKind::SRem; binary = true; break;
    case __dfsan::umin: kind = PKind::UMin; binary = true; break;
    case __dfsan::umax: kind = PKind::UMax; binary = true; break;
    case __dfsan::smin: kind = PKind::SMin; binary = true; break;
    case __dfsan::smax: kind = PKind::SMax; binary = true; break;
    case Shl: kind = PKind::Shl; binary = true; break;
    case LShr: kind = PKind::LShr; binary = true; break;
    case AShr: kind = PKind::AShr; binary = true; break;
    case __dfsan::ctlz: kind = PKind::Ctlz; unary = true; break;
    case __dfsan::cttz: kind = PKind::Cttz; unary = true; break;
    case And: kind = PKind::And; binary = true; break;
    case Or: kind = PKind::Or; binary = true; break;
    case Xor: kind = PKind::Xor; binary = true; break;
    case Neg: kind = PKind::Neg; unary = true; break;
    case Not: kind = PKind::Not; unary = true; break;
    case ZExt: kind = PKind::ZExt; unary = true; break;
    case SExt: kind = PKind::SExt; unary = true; break;
    default: break;
  }

  if (op == __dfsan::Extract || op_lo == Trunc) {
    // Commutative swapping in the runtime may leave a unary op's child in l2.
    dfsan_label child = info->l1 ? info->l1 : info->l2;
    uint64_t cval = info->l1 ? info->op1.i : info->op2.i;
    uint64_t off = (op == __dfsan::Extract) ? info->op2.i : 0;
    uint16_t child_bits = child != 0 && child < table_labels_
                              ? table_[child].size : info->size;
    if (child_bits > 64)
      return convert_slice(child, cval, child_bits, off, size);
    uint32_t a = conv_child(child, cval, child_bits);
    return a == kInvalidNode ? kInvalidNode
                             : add(PKind::Extract, size, a, kNoChild, off);
  }
  if (op == __dfsan::Concat) {
    if (info->l1 == 0 && info->l2 == 0) {
      fail(PredError::BadConcat);
      return kInvalidNode;
    }
    uint16_t l1_bits = 0, l2_bits = 0;
    if (info->l1 != 0) {
      if (info->l1 >= table_labels_) {
        fail(PredError::InvalidLabel);
        return kInvalidNode;
      }
      l1_bits = table_[info->l1].size;
      if (l1_bits > size) {
        fail(PredError::BadConcat);
        return kInvalidNode;
      }
    }
    if (info->l2 != 0) {
      if (info->l2 >= table_labels_) {
        fail(PredError::InvalidLabel);
        return kInvalidNode;
      }
      l2_bits = table_[info->l2].size;
      if (l2_bits > size) {
        fail(PredError::BadConcat);
        return kInvalidNode;
      }
    }
    if (info->l1 != 0 && info->l2 != 0 &&
        (uint32_t)l1_bits + l2_bits != size) {
      fail(PredError::BadConcat);
      return kInvalidNode;
    }
    uint16_t cbits1 = info->l1 ? l1_bits : (uint16_t)(size - l2_bits);
    uint16_t cbits2 = info->l2 ? l2_bits : (uint16_t)(size - l1_bits);
    uint32_t a = conv_child(info->l1, info->op1.i, cbits1);
    uint32_t b = conv_child(info->l2, info->op2.i, cbits2);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(PKind::Concat, size, a, b);
  }
  // strlen is a numeric value, not only a comparison operand. Lower it to
  // the exact prefix-nonzero sum so wrappers such as add/trunc/zext remain
  // input-dependent instead of falling through to opaque admission.
  if (op == __dfsan::fstrlen) {
    return convert_strlen_expr(*info);
  }
  if (op_lo == ICmp) {
    // A C memcmp result is specified only by its sign.  The scalar Memcmp node
    // therefore has a total canonical sign representation, but it is sound
    // only when consumed immediately by a comparison with zero.
    const bool left_memcmp =
        info->l1 != 0 && info->l1 < table_labels_ &&
        is_fmemcmp(table_[info->l1].op);
    const bool right_memcmp =
        info->l2 != 0 && info->l2 < table_labels_ &&
        is_fmemcmp(table_[info->l2].op);
    if ((left_memcmp && (info->l2 != 0 || info->op2.i != 0)) ||
        (right_memcmp && (info->l1 != 0 || info->op1.i != 0))) {
      fail(PredError::UnsupportedOp, static_cast<uint16_t>(op));
      return kInvalidNode;
    }
    if (left_memcmp && info->l2 == 0 &&
        table_[info->l1].size > 8) {
      return convert_fmemcmp_cmp(info, op, table_[info->l1]);
    }
    // String-op vs constant comparison: expand into byte reads so the scalar
    // interpreter can evaluate it (strlen > n, strchr/strstr != NULL).
    if (info->l1 != 0 && info->l1 < table_labels_ && info->l2 == 0) {
      const dfsan_label_info &so = table_[info->l1];
      uint16_t so_op = so.op & 0xff;
      if (so_op == __dfsan::fstrlen)
        return convert_strlen_cmp(info, op, so);
      if (so_op == __dfsan::fstrchr || so_op == __dfsan::fstrrchr)
        return convert_strchr_cmp(info, op, so);
      if (so_op == __dfsan::fstrstr)
        return convert_strstr_cmp(info, op, so);
    }
    uint32_t p = op >> 8;
    switch (p) {
      case bveq: kind = PKind::Equal; break;
      case bvneq: kind = PKind::Distinct; break;
      case bvugt: kind = PKind::Ugt; break;
      case bvuge: kind = PKind::Uge; break;
      case bvult: kind = PKind::Ult; break;
      case bvule: kind = PKind::Ule; break;
      case bvsgt: kind = PKind::Sgt; break;
      case bvsge: kind = PKind::Sge; break;
      case bvslt: kind = PKind::Slt; break;
      case bvsle: kind = PKind::Sle; break;
      default:
        fail(PredError::UnsupportedCompare);
        return kInvalidNode;
    }
    // A flen_count-family label compared against a *symbolic* operand: the
    // count's clamp must follow the candidate's request (a length-derived
    // expression such as `remaining`), not the trace-time constant recorded
    // in the label. Splice the other side into the Count clamp.
    const bool left_flen =
        info->l1 != 0 && info->l1 < table_labels_ &&
        is_flen_count_op(table_[info->l1].op & 0xff);
    const bool right_flen =
        info->l2 != 0 && info->l2 < table_labels_ &&
        is_flen_count_op(table_[info->l2].op & 0xff);
    if (left_flen && !right_flen && info->l2 != 0) {
      uint32_t other = conv_child(info->l2, info->op2.i, size);
      uint32_t clamp = label_depends_on(table_, table_labels_, info->l2,
                                        info->l1)
          ? add_const(table_[info->l1].op2.i & 0xFFFFFFFFull, size)
          : other;
      uint32_t count = build_flen_count(table_[info->l1], size, clamp);
      if (count == kInvalidNode || other == kInvalidNode) return kInvalidNode;
      return add(kind, size, count, other);
    }
    if (right_flen && !left_flen && info->l1 != 0) {
      uint32_t other = conv_child(info->l1, info->op1.i, size);
      uint32_t clamp = label_depends_on(table_, table_labels_, info->l1,
                                        info->l2)
          ? add_const(table_[info->l2].op2.i & 0xFFFFFFFFull, size)
          : other;
      uint32_t count = build_flen_count(table_[info->l2], size, clamp);
      if (count == kInvalidNode || other == kInvalidNode) return kInvalidNode;
      return add(kind, size, other, count);
    }
    uint32_t a = conv_child(info->l1, info->op1.i, size);
    uint32_t b = conv_child(info->l2, info->op2.i, size);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(kind, size, a, b);
  }
  if (op_lo == FCmp) {
    // Lower an FP comparison to an integer comparison over the IEEE-754 bit
    // patterns.  The FCmp label's op1/op2 carry the operands' concrete bits
    // (dfsan.cpp exempts FCmp from symbolic-operand zeroing); a symbolic
    // Load/Concat operand converts normally, a constant operand becomes a
    // Const of the literal's bits.
    return convert_fcmp(info, op);
  }
  if (op_lo == ZExt) {
    // A zero-extended single input byte is the getc-family read structure:
    // a missing byte is EOF (masked -1 at the width), matching `c != EOF`
    // evaluated at 32-bit. Lower to EofRead so short candidates route from
    // byte nodes into the length nodes instead of mispredicting 0xFF != -1.
    uint32_t a = conv_child(info->l1, info->op1.i, size);
    if (a == kInvalidNode) return kInvalidNode;
    const PNode &child_node = arena_->nodes[a];
    if (child_node.kind == PKind::Read && child_node.bits == 8)
      return add(PKind::EofRead, static_cast<uint16_t>(info->size),
                 kNoChild, kNoChild, child_node.value);
    return add(PKind::ZExt, size, a, kNoChild);
  }
  if (unary) {
    // Commutative swapping in the runtime may leave a unary op's child in l2.
    dfsan_label child = info->l1 ? info->l1 : info->l2;
    uint64_t cval = info->l1 ? info->op1.i : info->op2.i;
    uint32_t a = conv_child(child, cval, size);
    return a == kInvalidNode ? kInvalidNode : add(kind, size, a, kNoChild);
  }
  if (binary) {
    uint32_t a = conv_child(info->l1, info->op1.i, size);
    uint32_t b = conv_child(info->l2, info->op2.i, size);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(kind, size, a, b);
  }

  // Input-length boundary ops (flen_* / fsize): length-aware leaf nodes.
  // Their comparison semantics flow through the regular ICmp machinery
  // (EofRead's missing value is EOF, Count-family is a pure len function).
  if (op == __dfsan::fsize) {
    // stat st_size / lseek SEEK_END: the input length itself.
    return add(PKind::Len, 64, kNoChild, kNoChild, 0);
  }
  if (op == __dfsan::flen_eof) {
    // getc-family EOF read at missing offset k: input[k] or EOF(-1).
    return add(PKind::EofRead, static_cast<uint16_t>(info->size),
               kNoChild, kNoChild, info->op1.i);
  }
  if (is_flen_count_op(op)) {
    uint16_t bits = static_cast<uint16_t>(info->size);
    uint32_t clamp = add_const(info->op2.i & 0xFFFFFFFFull, bits);
    return build_flen_count(*info, bits, clamp);
  }

  // FP ops, string ops, Arg/Free, fmemcmp, GEP artifacts, ... : unsupported
  fail(PredError::UnsupportedOp, static_cast<uint16_t>(op));
  return kInvalidNode;
}

uint32_t RunConverter::build_flen_count(const dfsan_label_info &info,
                                        uint16_t bits, uint32_t clamp) {
  uint16_t op_lo = info.op & 0xff;
  if (op_lo == __dfsan::flen_count)
    return add(PKind::Count, bits, clamp, kNoChild, info.op1.i);
  if (op_lo == __dfsan::flen_count_neg1)
    return add(PKind::CountNeg1, bits, clamp, kNoChild, info.op1.i);
  if (op_lo == __dfsan::flen_count_elems) {
    // fread's nmemb may itself depend on the candidate length (XZ passes
    // fsize as nmemb).  The interceptor preserves that label in l1; use its
    // expression instead of freezing the trace-time nmemb in op2.  An
    // unsupported symbolic request fails conversion and is admitted
    // conservatively rather than evaluated with a stale constant.
    if (info.l1 != 0) {
      uint32_t dynamic_clamp = convert(info.l1);
      if (dynamic_clamp == kInvalidNode) return kInvalidNode;
      clamp = dynamic_clamp;
    }
    uint32_t item = add_const(info.op2.i >> 32, 32);
    return add(PKind::CountElems, bits, clamp, item, info.op1.i);
  }
  return kInvalidNode;
}

// Collect the input byte offsets covered by a string content label (in
// collection order; string_bytes sorts them).  Supports raw input bytes,
// Load (consecutive input bytes, byte count in l2), Concat, and fsubstr
// prefix mode (op2==0, first op1 bytes).  fsubstr suffix (op2==1, symbolic
// start) and non-input trees return false -> caller marks opaque.
bool RunConverter::collect_byte_offsets(dfsan_label label, size_t cap,
                                        std::vector<uint64_t> &offs) {
  if (offs.size() >= cap) return true;
  if (label == 0 || label >= table_labels_) return false;
  const dfsan_label_info &info = table_[label];
  uint32_t op = info.op;
  uint32_t op_lo = op & 0xff;
  if (op == 0) {
    if (offs.size() < cap) offs.push_back(info.op1.i);
    return true;
  }
  if (op_lo == Load) {
    if (info.l1 == 0 || info.l1 >= table_labels_ || info.l2 == 0 ||
        info.l2 > cap || table_[info.l1].op != 0)
      return false;
    uint64_t start = table_[info.l1].op1.i;
    for (uint64_t i = 0; i < info.l2; ++i) {
      if (offs.size() >= cap) return true;
      offs.push_back(start + i);
    }
    return true;
  }
  if (op_lo == Concat) {
    return collect_byte_offsets(info.l1, cap, offs) &&
           collect_byte_offsets(info.l2, cap, offs);
  }
  if (op_lo == fsubstr && info.op2.i == 0) {
    // prefix mode: first op1 bytes of the content
    if (!collect_byte_offsets(info.l1, cap, offs)) return false;
    if (offs.size() > (size_t)info.op1.i) offs.resize((size_t)info.op1.i);
    return true;
  }
  return false;
}

// Expand a content label into an ordered byte list (string position i ==
// out[i]).  Only consecutive input-byte spans are supported; anything else is
// rejected so the caller marks the predicate opaque (conservative admission).
bool RunConverter::collect_string_nodes(dfsan_label label, size_t cap,
                                         std::vector<StringByte> &out) {
  if (label == 0 || label >= table_labels_) return false;
  const dfsan_label_info &info = table_[label];
  const uint32_t op = info.op;
  const uint32_t op_lo = op & 0xff;

  auto append_const_bytes = [&](uint64_t value, size_t bytes) {
    if (bytes == 0 || bytes > cap - out.size()) return false;
    for (size_t i = 0; i < bytes; ++i) {
      uint32_t nd = add(PKind::Const, 8, kNoChild, kNoChild,
                        (value >> (8 * i)) & 0xff);
      if (nd == kInvalidNode) return false;
      out.push_back({nd, 0});
    }
    return true;
  };

  if (op == 0) {
    if (out.size() >= cap || info.size != 8) return false;
    uint32_t nd = add(PKind::Read, 8, kNoChild, kNoChild, info.op1.i);
    if (nd == kInvalidNode) return false;
    out.push_back({nd, (uint32_t)info.op1.i});
    return true;
  }
  if (op_lo == Load) {
    if (info.l1 == 0 || info.l1 >= table_labels_ || info.l2 == 0 ||
        info.l2 > cap - out.size() || table_[info.l1].op != 0)
      return false;
    const uint64_t start = table_[info.l1].op1.i;
    for (uint64_t i = 0; i < info.l2; ++i) {
      uint32_t nd = add(PKind::Read, 8, kNoChild, kNoChild, start + i);
      if (nd == kInvalidNode) return false;
      out.push_back({nd, (uint32_t)(start + i)});
    }
    return true;
  }
  if (op_lo == Concat) {
    if (info.size == 0 || (info.size & 7) != 0) return false;
    uint16_t low_bits = 0;
    uint16_t high_bits = 0;
    if (info.l1 != 0) {
      if (info.l1 >= table_labels_) return false;
      low_bits = table_[info.l1].size;
    }
    if (info.l2 != 0) {
      if (info.l2 >= table_labels_) return false;
      high_bits = table_[info.l2].size;
    }
    if (info.l1 == 0) low_bits = info.size - high_bits;
    if (info.l2 == 0) high_bits = info.size - low_bits;
    if (low_bits == 0 || high_bits == 0 ||
        static_cast<uint32_t>(low_bits) + high_bits != info.size)
      return false;
    if (info.l1 != 0) {
      size_t before = out.size();
      if (!collect_string_nodes(info.l1, cap, out) ||
          out.size() - before != low_bits / 8)
        return false;
    } else if (!append_const_bytes(info.op1.i, low_bits / 8)) {
      return false;
    }
    if (info.l2 != 0) {
      size_t before = out.size();
      if (!collect_string_nodes(info.l2, cap, out) ||
          out.size() - before != high_bits / 8)
        return false;
    } else if (!append_const_bytes(info.op2.i, high_bits / 8)) {
      return false;
    }
    return true;
  }
  if (op_lo == Trunc || op_lo == BitCast) {
    dfsan_label child = info.l1 ? info.l1 : info.l2;
    if (child == 0 || child >= table_labels_ || (info.size & 7) != 0)
      return false;
    std::vector<StringByte> child_bytes;
    if (!collect_string_nodes(child, cap, child_bytes) ||
        child_bytes.size() < info.size / 8)
      return false;
    out.insert(out.end(), child_bytes.begin(),
               child_bytes.begin() + info.size / 8);
    return out.size() <= cap;
  }
  if (op_lo == __dfsan::fsubstr && info.op2.i == 0) {
    if (!collect_string_nodes(info.l1, cap, out) ||
        out.size() < info.op1.i)
      return false;
    out.resize((size_t)info.op1.i);
    return true;
  }
  return false;
}

bool RunConverter::string_bytes(dfsan_label content, size_t max_bytes,
                                std::vector<StringByte> &out) {
  out.clear();
  return collect_string_nodes(content, max_bytes, out) && !out.empty();
}

uint32_t RunConverter::convert_strlen_expr(
    const dfsan_label_info &strlen_info) {
  const uint16_t bits = strlen_info.size;
  if (bits == 0 || bits > 64) {
    fail(PredError::InvalidWidth, static_cast<uint16_t>(strlen_info.op));
    return kInvalidNode;
  }
  // A program-provided terminator makes the length concrete by definition;
  // only input-derived terminators need the byte-level expression below.
  if (strlen_info.op1.i == 0)
    return add_const(strlen_info.op2.i, bits);
  if (strlen_info.op2.i > kMaxStrlenBytes) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(strlen_info.op));
    return kInvalidNode;
  }

  std::vector<StringByte> bytes;
  if (!string_bytes(strlen_info.l2, kMaxStrlenBytes, bytes) ||
      strlen_info.op2.i >= bytes.size()) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(strlen_info.op));
    return kInvalidNode;
  }

  uint32_t length = add_const(0, bits);
  uint32_t prefix = add_const(1, 8);
  uint32_t zero = add_const(0, 8);
  if (length == kInvalidNode || prefix == kInvalidNode ||
      zero == kInvalidNode)
    return kInvalidNode;
  for (const StringByte &byte : bytes) {
    uint32_t term = add(PKind::ZExt, bits, prefix, kNoChild);
    length = add(PKind::Add, bits, length, term);
    uint32_t nonzero = add(PKind::Distinct, 8, byte.node, zero);
    prefix = add(PKind::And, 8, prefix, nonzero);
    if (length == kInvalidNode || nonzero == kInvalidNode ||
        prefix == kInvalidNode)
      return kInvalidNode;
  }
  return length;
}

// strlen(s) OP n, expanded into byte-nonzero constraints over the string's
// content bytes.  `strlen_info` is the fstrlen label (l1=0, l2=content,
// op1=null_from_input, op2=concrete length).
uint32_t RunConverter::convert_strlen_cmp(const dfsan_label_info *info,
                                          uint32_t op,
                                          const dfsan_label_info &si) {
  uint32_t p = op >> 8;
  uint64_t n = info->op2.i;
  if (n == 0 && (p == bvuge || p == bvsge)) return add_const(1, 8);
  if (n == 0 && (p == bvult || p == bvslt)) return add_const(0, 8);
  // Programmatic NUL (null_from_input == 0): the length is concrete.
  if (si.op1.i == 0) {
    uint32_t len = add_const(si.op2.i, info->size);
    uint32_t cnst = add_const(n, info->size);
    PKind k;
    switch (p) {
      case bveq: k = PKind::Equal; break;
      case bvneq: k = PKind::Distinct; break;
      case bvugt: k = PKind::Ugt; break;
      case bvuge: k = PKind::Uge; break;
      case bvult: k = PKind::Ult; break;
      case bvule: k = PKind::Ule; break;
      case bvsgt: k = PKind::Sgt; break;
      case bvsge: k = PKind::Sge; break;
      case bvslt: k = PKind::Slt; break;
      case bvsle: k = PKind::Sle; break;
      default:
        fail(PredError::UnsupportedCompare);
        return kInvalidNode;
    }
    return add(k, info->size, len, cnst);
  }
  if (n > kMaxStrlenBytes) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  std::vector<StringByte> bytes;
  if (!string_bytes(si.l2, kMaxStrlenBytes, bytes)) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  //  len > n  : bytes 0..n   all nonzero          (n+1 reads)
  //  len >= n : bytes 0..n-1 all nonzero          (n reads)
  //  len < n  : some byte 0..n-1 is zero          (n reads)
  //  len <= n : some byte 0..n   is zero          (n+1 reads)
  //  len == n : bytes 0..n-1 nonzero && byte n zero (n+1 reads)
  //  len != n : some byte 0..n-1 zero || byte n nonzero (n+1 reads)
  bool need_n1 = (p == bvugt || p == bvule || p == bveq || p == bvneq);
  uint64_t need = need_n1 ? n + 1 : n;
  if (need == 0 || need > bytes.size()) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  std::vector<uint32_t> zero(need), nz(need);
  for (uint64_t i = 0; i < need; ++i) {
    uint32_t c0 = add_const(0, 8);
    zero[i] = add(PKind::Equal, 8, bytes[i].node, c0);
    nz[i] = add(PKind::Distinct, 8, bytes[i].node, c0);
  }
  uint64_t lo = 0, hi = 0;
  bool use_nz = false;
  uint32_t extra = kInvalidNode;
  switch (p) {
    case bvugt: case bvsgt: lo = 0; hi = n; use_nz = true; break;
    case bvuge: case bvsge: lo = 0; hi = n - 1; use_nz = true; break;
    case bvult: case bvslt: lo = 0; hi = n - 1; use_nz = false; break;
    case bvule: case bvsle: lo = 0; hi = n; use_nz = false; break;
    case bveq: lo = 0; hi = n - 1; use_nz = true; extra = zero[n]; break;
    case bvneq: lo = 0; hi = n - 1; use_nz = false; extra = nz[n]; break;
    default:
      fail(PredError::UnsupportedCompare);
      return kInvalidNode;
  }
  uint32_t acc = kInvalidNode;
  for (uint64_t i = lo; i <= hi; ++i) {
    uint32_t t = use_nz ? nz[i] : zero[i];
    acc = (acc == kInvalidNode)
              ? t
              : (use_nz ? add(PKind::And, 8, acc, t)
                        : add(PKind::Or, 8, acc, t));
  }
  if (acc != kInvalidNode && extra != kInvalidNode) {
    acc = (p == bveq) ? add(PKind::And, 8, acc, extra)
                      : add(PKind::Or, 8, acc, extra);
  }
  if (acc == kInvalidNode) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  return acc;
}

// strchr(s, c) != NULL / == NULL, expanded into an existence disjunction over
// the content bytes.  `chr_info` is the fstrchr label (op2 low byte = needle).
uint32_t RunConverter::convert_strchr_cmp(const dfsan_label_info *info,
                                          uint32_t op,
                                          const dfsan_label_info &ci) {
  uint32_t p = op >> 8;
  bool want_found = (p == bvneq);
  bool want_miss = (p == bveq);
  if (!want_found && !want_miss) {
    fail(PredError::UnsupportedCompare);
    return kInvalidNode;
  }
  if (ci.l2 != 0) {  // symbolic needle: collected but not scalar-solvable
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(ci.op));
    return kInvalidNode;
  }
  uint8_t c = ci.op2.i & 0xff;
  std::vector<StringByte> bytes;
  if (!string_bytes(ci.l1, kMaxSearchBytes, bytes) || bytes.empty()) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(ci.op));
    return kInvalidNode;
  }
  uint32_t cnode = add_const(c, 8);
  uint32_t acc = kInvalidNode;
  for (size_t i = 0; i < bytes.size(); ++i) {
    uint32_t t = want_found
                     ? add(PKind::Equal, 8, bytes[i].node, cnode)
                     : add(PKind::Distinct, 8, bytes[i].node, cnode);
    acc = (acc == kInvalidNode)
              ? t
              : (want_found ? add(PKind::Or, 8, acc, t)
                            : add(PKind::And, 8, acc, t));
  }
  if (acc == kInvalidNode) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(ci.op));
    return kInvalidNode;
  }
  return acc;
}

// strstr(h, needle) != NULL / == NULL.  The concrete needle bytes are packed
// into the label's op2 by the runtime (dfsan_custom.cpp __dfsw_strstr).
uint32_t RunConverter::convert_strstr_cmp(const dfsan_label_info *info,
                                          uint32_t op,
                                          const dfsan_label_info &si) {
  uint32_t p = op >> 8;
  bool want_found = (p == bvneq);
  bool want_miss = (p == bveq);
  if (!want_found && !want_miss) {
    fail(PredError::UnsupportedCompare);
    return kInvalidNode;
  }
  if (si.l2 != 0) {  // symbolic needle
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  uint32_t nlen = si.size;  // concrete needle byte count
  uint64_t packed = si.op2.i;
  if (nlen == 0 || nlen > 8) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  std::vector<StringByte> bytes;
  if (!string_bytes(si.l1, kMaxSearchBytes, bytes)) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  if (bytes.size() < nlen) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  uint32_t needle[8];
  for (uint32_t k = 0; k < nlen; ++k)
    needle[k] = add_const((packed >> (8 * k)) & 0xff, 8);
  size_t max_starts =
      std::min<size_t>(bytes.size() - nlen + 1, kMaxSearchBytes);
  uint32_t acc = kInvalidNode;
  for (size_t s = 0; s < max_starts; ++s) {
    uint32_t inner = kInvalidNode;
    for (uint32_t k = 0; k < nlen; ++k) {
      uint32_t t = want_found
                       ? add(PKind::Equal, 8, bytes[s + k].node, needle[k])
                       : add(PKind::Distinct, 8, bytes[s + k].node, needle[k]);
      inner = (inner == kInvalidNode)
                  ? t
                  : (want_found ? add(PKind::And, 8, inner, t)
                                : add(PKind::Or, 8, inner, t));
    }
    acc = (acc == kInvalidNode)
              ? inner
              : (want_found ? add(PKind::Or, 8, acc, inner)
                            : add(PKind::And, 8, acc, inner));
  }
  if (acc == kInvalidNode) {
    fail(PredError::UnsupportedOp, static_cast<uint16_t>(si.op));
    return kInvalidNode;
  }
  return acc;
}

uint32_t RunConverter::convert_fmemcmp_cmp(
    const dfsan_label_info *info, uint32_t op,
    const dfsan_label_info &memcmp_info) {
  const uint32_t n = memcmp_info.size;
  if (n == 0 || n > 16) {
    fail(PredError::InvalidWidth, static_cast<uint16_t>(memcmp_info.op));
    return kInvalidNode;
  }

  auto constant_bytes = [&](bool operand2, std::vector<StringByte> &out) {
    if (!fmemcmp_operand_captured(memcmp_info.op, operand2)) {
      fail(PredError::UncapturedMemcmpOperand, memcmp_info.op);
      return false;
    }
    uint64_t low = operand2 ? memcmp_info.op2.i : memcmp_info.op1.i;
    uint64_t high = operand2 ? memcmp_info.op2_hi : memcmp_info.op1_hi;
    for (uint32_t i = 0; i < n; ++i) {
      uint64_t word = i < 8 ? low : high;
      uint32_t byte = static_cast<uint32_t>((word >> (8 * (i % 8))) & 0xff);
      out.push_back({add_const(byte, 8), 0});
    }
    return true;
  };

  std::vector<StringByte> lhs, rhs;
  if (memcmp_info.l1 == 0) {
    if (!constant_bytes(false, lhs)) return kInvalidNode;
  } else if (!string_bytes(memcmp_info.l1, n, lhs)) {
    fail(PredError::UnsupportedOp, memcmp_info.op);
    return kInvalidNode;
  }
  if (memcmp_info.l2 == 0) {
    if (!constant_bytes(true, rhs)) return kInvalidNode;
  } else if (!string_bytes(memcmp_info.l2, n, rhs)) {
    fail(PredError::UnsupportedOp, memcmp_info.op);
    return kInvalidNode;
  }
  if (lhs.size() != n || rhs.size() != n) {
    fail(PredError::UnsupportedOp, memcmp_info.op);
    return kInvalidNode;
  }

  // The C memcmp result is the sign of the first differing unsigned byte.
  // Build the three mutually exclusive outcomes without creating a wide
  // integer node: less-than, equal, and greater-than.
  uint32_t equal_prefix = add_const(1, 8);
  uint32_t less = add_const(0, 8);
  uint32_t greater = add_const(0, 8);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t eq = add(PKind::Equal, 8, lhs[i].node, rhs[i].node);
    uint32_t lt = add(PKind::Ult, 8, lhs[i].node, rhs[i].node);
    uint32_t gt = add(PKind::Ugt, 8, lhs[i].node, rhs[i].node);
    less = add(PKind::Or, 8, less,
               add(PKind::And, 8, equal_prefix, lt));
    greater = add(PKind::Or, 8, greater,
                  add(PKind::And, 8, equal_prefix, gt));
    equal_prefix = add(PKind::And, 8, equal_prefix, eq);
  }

  switch (op >> 8) {
    case bveq: return equal_prefix;
    case bvneq: return add(PKind::Or, 8, less, greater);
    case bvult: case bvslt: return less;
    case bvule: case bvsle: return add(PKind::Or, 8, less, equal_prefix);
    case bvugt: case bvsgt: return greater;
    case bvuge: case bvsge: return add(PKind::Or, 8, greater, equal_prefix);
    default:
      fail(PredError::UnsupportedCompare, static_cast<uint16_t>(op));
      return kInvalidNode;
  }
}

// FP comparison lowered to integer comparison over IEEE-754 bit patterns
// (total-order transform), matching LLVM FCmp semantics including NaN and ±0.
uint32_t RunConverter::fp_is_nan(uint32_t a, uint16_t w) {
  uint16_t mant_bits = w == 64 ? 52 : 23;
  uint64_t exp_mask = w == 64 ? 0x7ff : 0xff;
  uint64_t mant_mask = w == 64 ? 0xfffffffffffffull : 0x7fffffull;
  uint32_t exp = add(PKind::And, w,
                     add(PKind::LShr, w, a, add_const(mant_bits, w), 0),
                     add_const(exp_mask, w));
  uint32_t mant = add(PKind::And, w, a, add_const(mant_mask, w), 0);
  return add(PKind::And, w, add(PKind::Equal, w, exp, add_const(exp_mask, w)),
             add(PKind::Distinct, w, mant, add_const(0, w)));
}

uint32_t RunConverter::fp_is_zero(uint32_t a, uint16_t w) {
  uint64_t lower = (1ull << (w - 1)) - 1;  // ~sign bit
  return add(PKind::Equal, w, add(PKind::And, w, a, add_const(lower, w), 0),
             add_const(0, w));
}

uint32_t RunConverter::fp_total_order(uint32_t a, uint16_t w) {
  uint64_t signbit = 1ull << (w - 1);
  uint32_t sign = add(PKind::LShr, w, a, add_const(w - 1, w), 0);
  // mask = sign ? ~0 : signbit  (negatives flip all bits, positives set sign)
  uint32_t mask = add(PKind::Or, w, add(PKind::Sub, w, add_const(0, w), sign),
                      add_const(signbit, w));
  return add(PKind::Xor, w, a, mask);
}

uint32_t RunConverter::convert_fcmp(const dfsan_label_info *info,
                                    uint32_t op) {
  uint32_t p = op >> 8;
  if (p > 15) {
    fail(PredError::UnsupportedCompare);
    return kInvalidNode;
  }
  uint16_t w = info->size;
  if (w != 32 && w != 64) {
    fail(PredError::InvalidWidth);
    return kInvalidNode;
  }
  // Symbolic operand (Load/Concat) converts normally; a constant operand uses
  // the label's stored IEEE bits (the literal being compared against).
  uint32_t a = conv_child(info->l1, info->op1.i, w);
  uint32_t b = conv_child(info->l2, info->op2.i, w);
  if (a == kInvalidNode || b == kInvalidNode) return kInvalidNode;
  uint32_t nan_a = fp_is_nan(a, w), nan_b = fp_is_nan(b, w);
  uint32_t zero_a = fp_is_zero(a, w), zero_b = fp_is_zero(b, w);
  uint32_t to_a = fp_total_order(a, w), to_b = fp_total_order(b, w);
  uint32_t ord = add(PKind::And, w, add(PKind::Not, w, nan_a, kNoChild),
                     add(PKind::Not, w, nan_b, kNoChild));
  uint32_t eq = add(PKind::Or, w, add(PKind::And, w, zero_a, zero_b),
                    add(PKind::And, w, ord, add(PKind::Equal, w, a, b)));
  uint32_t both_zero = add(PKind::And, w, zero_a, zero_b);
  uint32_t nz = add(PKind::Not, w, both_zero, kNoChild);
  uint32_t gt = add(PKind::And, w, ord,
                    add(PKind::And, w, add(PKind::Ugt, w, to_a, to_b), nz));
  uint32_t lt = add(PKind::And, w, ord,
                    add(PKind::And, w, add(PKind::Ult, w, to_a, to_b), nz));
  uint32_t ge = add(PKind::And, w, ord,
                    add(PKind::Or, w, add(PKind::Ugt, w, to_a, to_b), eq));
  uint32_t le = add(PKind::And, w, ord,
                    add(PKind::Or, w, add(PKind::Ult, w, to_a, to_b), eq));
  uint32_t uno = add(PKind::Not, w, ord, kNoChild);
  switch (p) {
    case 0:  return add_const(0, w);                                           // FALSE
    case 1:  return eq;                                                        // OEQ
    case 2:  return gt;                                                        // OGT
    case 3:  return ge;                                                        // OGE
    case 4:  return lt;                                                        // OLT
    case 5:  return le;                                                        // OLE
    case 6:  return add(PKind::And, w, ord, add(PKind::Not, w, eq, kNoChild)); // ONE
    case 7:  return ord;                                                       // ORD
    case 8:  return uno;                                                       // UNO
    case 9:  return add(PKind::Or, w, uno, eq);                                // UEQ
    case 10: return add(PKind::Or, w, uno, gt);                                // UGT
    case 11: return add(PKind::Or, w, uno, ge);                                // UGE
    case 12: return add(PKind::Or, w, uno, lt);                                // ULT
    case 13: return add(PKind::Or, w, uno, le);                                // ULE
    case 14: return add(PKind::Not, w, eq, kNoChild);                          // UNE
    case 15: return add_const(1, w);                                           // TRUE
    default: fail(PredError::UnsupportedCompare); return kInvalidNode;
  }
}

Predicate RunConverter::conv(uint32_t label) {
  Predicate pred;
  error_ = PredError::None;
  error_op_ = 0;
  root_label_ = label;
  if (label == 0) {
    pred.opaque = true;
    pred.error = PredError::InvalidRoot;
    return pred;
  }
  if (label == kInitializingLabel) {
    pred.opaque = true;
    pred.error = PredError::InitializingLabel;
    return pred;
  }
  if (label >= table_labels_) {
    pred.opaque = true;
    pred.error = PredError::InvalidRoot;
    return pred;
  }

  predicate_start_ = arena_->nodes.size();
  pred.root = convert(label);
  if (pred.root == kInvalidNode) {
    pred.root = 0;
    pred.opaque = true;
    pred.error = error_ == PredError::None ? PredError::InvalidRoot : error_;
    pred.error_op = error_op_;
    return pred;
  }

  std::unordered_set<uint32_t> seen;
  std::vector<uint32_t> stack = {pred.root};
  while (!stack.empty()) {
    uint32_t i = stack.back();
    stack.pop_back();
    if (!seen.insert(i).second) continue;
    const PNode &nd = arena_->nodes[i];
    if (nd.kind == PKind::Read)
      pred.reads.emplace_back((uint32_t)nd.value, nd.bits / 8);
    if (nd.a != kNoChild) stack.push_back(nd.a);
    if (nd.b != kNoChild) stack.push_back(nd.b);
  }
  std::sort(pred.reads.begin(), pred.reads.end());
  pred.reads.erase(std::unique(pred.reads.begin(), pred.reads.end()),
                   pred.reads.end());
  return pred;
}

bool RunConverter::expand_fold(uint32_t first_label, uint16_t count,
                               uint16_t start,
                               std::vector<Predicate> *out) {
  if (out == nullptr || start >= count) return false;
  const size_t nodes_ck = arena_->nodes.size();
  Predicate first = conv(first_label);
  if (first.opaque) {
    // conv already rolled back its own nodes on failure; resize is a
    // no-op backstop for the memoized-root case.
    arena_->nodes.resize(nodes_ck);
    for (uint16_t k = start; k < count; ++k) {
      Predicate p;
      p.opaque = true;
      p.error = first.error;
      p.error_op = first.error_op;
      out->push_back(p);
    }
    return false;
  }

  // Collect the template DAG in post-order (children before parents), each
  // node once even if shared.
  std::vector<uint32_t> post;
  std::unordered_set<uint32_t> seen;
  std::vector<std::pair<uint32_t, bool>> st = {{first.root, false}};
  while (!st.empty()) {
    auto [i, expanded] = st.back();
    st.pop_back();
    if (expanded) {
      post.push_back(i);
      continue;
    }
    if (!seen.insert(i).second) continue;
    st.push_back({i, true});
    const PNode &nd = arena_->nodes[i];
    if (nd.b != kNoChild) st.push_back({nd.b, false});
    if (nd.a != kNoChild) st.push_back({nd.a, false});
  }

  // Determine the fold dimension. Byte-advancing shapes (getc loops) advance
  // the single Read/EofRead leaf; loop-bound shapes (`i < n` vs flen_count)
  // advance the constant side (the loop counter), which converts to the sole
  // Const child of the comparison root.
  bool has_read_leaf = false;
  for (uint32_t orig : post) {
    const PNode &nd = arena_->nodes[orig];
    if (nd.kind == PKind::Read || nd.kind == PKind::EofRead) {
      has_read_leaf = true;
      break;
    }
  }
  uint32_t const_child = kNoChild;
  if (!has_read_leaf) {
    const PNode &root_nd = arena_->nodes[first.root];
    for (uint32_t c : {root_nd.a, root_nd.b}) {
      if (c != kNoChild && arena_->nodes[c].kind == PKind::Const) {
        const_child = c;
        break;
      }
    }
  }

  const size_t clone_ck = arena_->nodes.size();
  predicate_start_ = clone_ck;
  std::unordered_map<uint32_t, uint32_t> map;
  for (uint16_t k = start; k < count; ++k) {
    map.clear();
    bool failed = false;
    for (uint32_t orig : post) {
      const PNode &nd = arena_->nodes[orig];
      uint64_t value = nd.value;
      if (k > 0 && (nd.kind == PKind::Read || nd.kind == PKind::EofRead))
        value += k;
      else if (k > 0 && orig == const_child)
        value += k;
      uint32_t na = nd.a == kNoChild ? kNoChild : map[nd.a];
      uint32_t nb = nd.b == kNoChild ? kNoChild : map[nd.b];
      uint32_t idx = add(nd.kind, nd.bits, na, nb, value);
      if (idx == kInvalidNode) {
        failed = true;
        break;
      }
      map[orig] = idx;
    }
    if (failed) {
      // Arena budget exhausted: roll back this fold's clones and mark the
      // remaining predicates opaque (conservative admission).
      arena_->nodes.resize(clone_ck);
      for (uint16_t j = k; j < count; ++j) {
        Predicate p;
        p.opaque = true;
        p.error = PredError::ArenaLimit;
        out->push_back(p);
      }
      return false;
    }
    // Reads collection follows conv()'s rule: PKind::Read leaves only
    // (EofRead/Count-family are length semantics, not input reads).
    Predicate p;
    p.root = map[first.root];
    std::unordered_set<uint32_t> rseen;
    std::vector<uint32_t> rstack = {p.root};
    while (!rstack.empty()) {
      uint32_t i = rstack.back();
      rstack.pop_back();
      if (!rseen.insert(i).second) continue;
      const PNode &nd = arena_->nodes[i];
      if (nd.kind == PKind::Read)
        p.reads.emplace_back((uint32_t)nd.value, nd.bits / 8);
      if (nd.a != kNoChild) rstack.push_back(nd.a);
      if (nd.b != kNoChild) rstack.push_back(nd.b);
    }
    std::sort(p.reads.begin(), p.reads.end());
    p.reads.erase(std::unique(p.reads.begin(), p.reads.end()),
                  p.reads.end());
    out->push_back(p);
  }
  return true;
}

namespace {
inline uint64_t mask_bits(uint64_t v, uint16_t bits) {
  return bits >= 64 ? v : (v & ((1ull << bits) - 1));
}
inline int64_t sext_bits(uint64_t v, uint16_t bits) {
  if (bits >= 64) return (int64_t)v;
  uint64_t m = 1ull << (bits - 1);
  return (int64_t)((v ^ m) - m);
}

template <typename T>
static T fp_from_bits(uint64_t value) {
  T result;
  using U = typename std::conditional<sizeof(T) == 4, uint32_t, uint64_t>::type;
  U raw = static_cast<U>(value);
  std::memcpy(&result, &raw, sizeof(result));
  return result;
}

template <typename T>
static uint64_t fp_to_bits(T value) {
  using U = typename std::conditional<sizeof(T) == 4, uint32_t, uint64_t>::type;
  U raw = 0;
  std::memcpy(&raw, &value, sizeof(raw));
  return static_cast<uint64_t>(raw);
}

template <typename T>
static T fp_round_mode(T value, uint64_t mode) {
  switch (mode) {
    case 0: return std::round(value);  // nearest, ties away
    case 1: return std::nearbyint(value); // nearest, ties to even
    case 2: return std::ceil(value);
    case 3: return std::floor(value);
    case 4: return std::trunc(value);
    default: return std::nearbyint(value);
  }
}

static bool eval_fp_cast(PKind kind, uint16_t out_bits, uint16_t input_bits,
                         uint64_t a, uint64_t *out) {
  if (out_bits != 32 && out_bits != 64) return false;
  if (kind == PKind::FpTrunc) {
    if (input_bits != 64 || out_bits != 32) return false;
    return *out = fp_to_bits(static_cast<float>(fp_from_bits<double>(a))), true;
  }
  if (kind == PKind::FpExt) {
    if (input_bits != 32 || out_bits != 64) return false;
    return *out = fp_to_bits(static_cast<double>(fp_from_bits<float>(a))), true;
  }
  if (kind == PKind::FpToUI || kind == PKind::FpToSI) {
    if (input_bits != 32 && input_bits != 64) return false;
    long double value = input_bits == 32
        ? static_cast<long double>(fp_from_bits<float>(a))
        : static_cast<long double>(fp_from_bits<double>(a));
    if (!std::isfinite(value)) return false;
    if (kind == PKind::FpToUI) {
      long double limit = std::ldexp(1.0L, out_bits);
      if (value < 0 || value >= limit) return false;
      *out = mask_bits(static_cast<uint64_t>(value), out_bits);
    } else {
      long double limit = std::ldexp(1.0L, out_bits - 1);
      if (value < -limit || value >= limit) return false;
      *out = mask_bits(static_cast<uint64_t>(static_cast<int64_t>(value)),
                       out_bits);
    }
    return true;
  }
  if (kind == PKind::FpToFP || kind == PKind::FpSIToFP) {
    long double value = kind == PKind::FpToFP
        ? static_cast<long double>(mask_bits(a, input_bits))
        : static_cast<long double>(sext_bits(a, input_bits));
    if (out_bits == 32)
      *out = fp_to_bits(static_cast<float>(value));
    else
      *out = fp_to_bits(static_cast<double>(value));
    return true;
  }
  return false;
}

static bool eval_fp_unary(PKind kind, uint16_t bits, uint64_t a,
                          uint64_t mode, uint64_t *out) {
  if (bits != 32 && bits != 64) return false;
  if (kind == PKind::FpLrint) {
    long double value = bits == 32
        ? static_cast<long double>(fp_from_bits<float>(a))
        : static_cast<long double>(fp_from_bits<double>(a));
    // The runtime wrapper is lrint/lrintf with the default RNE mode.  Use
    // nearbyint rather than the trace-time integer result so the input
    // dependency remains live during CheckInput.
    long double rounded = std::nearbyint(value);
    if (rounded > static_cast<long double>(std::numeric_limits<int64_t>::max()) ||
        rounded < static_cast<long double>(std::numeric_limits<int64_t>::min()))
      return false;
    *out = static_cast<uint64_t>(static_cast<int64_t>(rounded));
    return true;
  }
  if (kind == PKind::FpIsNan || kind == PKind::FpIsInf ||
      kind == PKind::FpIsFinite || kind == PKind::FpSignBit) {
    bool result;
    if (bits == 32) {
      float value = fp_from_bits<float>(a);
      result = kind == PKind::FpIsNan ? std::isnan(value) :
          kind == PKind::FpIsInf ? std::isinf(value) :
          kind == PKind::FpIsFinite ? std::isfinite(value) :
          std::signbit(value);
    } else {
      double value = fp_from_bits<double>(a);
      result = kind == PKind::FpIsNan ? std::isnan(value) :
          kind == PKind::FpIsInf ? std::isinf(value) :
          kind == PKind::FpIsFinite ? std::isfinite(value) :
          std::signbit(value);
    }
    *out = result ? 1 : 0;
    return true;
  }
  if (bits == 32) {
    float value = fp_from_bits<float>(a), result;
    switch (kind) {
      case PKind::FpNeg: result = -value; break;
      case PKind::FpAbs: result = std::fabs(value); break;
      case PKind::FpSqrt: result = std::sqrt(value); break;
      case PKind::FpRound: result = fp_round_mode(value, mode); break;
      case PKind::FpExp: result = std::exp(value); break;
      case PKind::FpExp2: result = std::exp2(value); break;
      case PKind::FpLog: result = std::log(value); break;
      case PKind::FpLog2: result = std::log2(value); break;
      case PKind::FpLog10: result = std::log10(value); break;
      case PKind::FpLog1p: result = std::log1p(value); break;
      default: return false;
    }
    *out = fp_to_bits(result);
  } else {
    double value = fp_from_bits<double>(a), result;
    switch (kind) {
      case PKind::FpNeg: result = -value; break;
      case PKind::FpAbs: result = std::fabs(value); break;
      case PKind::FpSqrt: result = std::sqrt(value); break;
      case PKind::FpRound: result = fp_round_mode(value, mode); break;
      case PKind::FpExp: result = std::exp(value); break;
      case PKind::FpExp2: result = std::exp2(value); break;
      case PKind::FpLog: result = std::log(value); break;
      case PKind::FpLog2: result = std::log2(value); break;
      case PKind::FpLog10: result = std::log10(value); break;
      case PKind::FpLog1p: result = std::log1p(value); break;
      default: return false;
    }
    *out = fp_to_bits(result);
  }
  return true;
}

static bool eval_fp_binary(PKind kind, uint16_t bits, uint64_t a, uint64_t b,
                           uint64_t *out) {
  if (bits != 32 && bits != 64) return false;
  if (bits == 32) {
    float av = fp_from_bits<float>(a), bv = fp_from_bits<float>(b), result;
    switch (kind) {
      case PKind::FpAdd: result = av + bv; break;
      case PKind::FpSub: result = av - bv; break;
      case PKind::FpMul: result = av * bv; break;
      case PKind::FpDiv: result = av / bv; break;
      case PKind::FpRem: result = std::fmod(av, bv); break;
      case PKind::FpMin: result = std::fmin(av, bv); break;
      case PKind::FpMax: result = std::fmax(av, bv); break;
      case PKind::FpCopySign: result = std::copysign(av, bv); break;
      case PKind::FpPow: result = std::pow(av, bv); break;
      default: return false;
    }
    *out = fp_to_bits(result);
  } else {
    double av = fp_from_bits<double>(a), bv = fp_from_bits<double>(b), result;
    switch (kind) {
      case PKind::FpAdd: result = av + bv; break;
      case PKind::FpSub: result = av - bv; break;
      case PKind::FpMul: result = av * bv; break;
      case PKind::FpDiv: result = av / bv; break;
      case PKind::FpRem: result = std::fmod(av, bv); break;
      case PKind::FpMin: result = std::fmin(av, bv); break;
      case PKind::FpMax: result = std::fmax(av, bv); break;
      case PKind::FpCopySign: result = std::copysign(av, bv); break;
      case PKind::FpPow: result = std::pow(av, bv); break;
      default: return false;
    }
    *out = fp_to_bits(result);
  }
  return true;
}
}  // namespace

bool eval_predicate(const PredArena &arena, const Predicate &pred,
                    const uint8_t *input, uint32_t len, uint64_t *out,
                    EvalContext *context, EvalStats *stats) {
  if (stats) stats->predicate_calls += 1;
  if (pred.opaque || pred.root >= arena.nodes.size()) return false;
  const auto &nodes = arena.nodes;
  static thread_local EvalContext local_context;
  if (!context) {
    context = &local_context;
    context->Reset();
  }
  // A post-order arena keeps every reachable child below its parent, so the
  // whole root-reachable DAG fits in [0, pred.root]; size the cache once per
  // root instead of growing per node.  The arrays only grow; Reset() changes
  // generation_ rather than clearing them.
  if (context->stamps_.size() <= pred.root) {
    context->values_.resize(pred.root + 1, 0);
    context->stamps_.resize(pred.root + 1, 0);
  }
  const uint32_t stamp = context->generation_;
  context->stack_.push_back({pred.root, false});

  while (!context->stack_.empty()) {
    auto frame = context->stack_.back();
    context->stack_.pop_back();
    if (frame.first >= nodes.size()) return false;
    if (context->stamps_[frame.first] == stamp) {
      if (stats) stats->cache_hits += 1;
      continue;
    }
    const PNode &nd = nodes[frame.first];
    if (!frame.second) {
      context->stack_.push_back({frame.first, true});
      if (nd.b != kNoChild) context->stack_.push_back({nd.b, false});
      if (nd.a != kNoChild) context->stack_.push_back({nd.a, false});
      continue;
    }

    uint64_t a = 0, b = 0;
    if (nd.a != kNoChild) {
      if (nd.a >= context->stamps_.size() ||
          context->stamps_[nd.a] != stamp)
        return false;
      a = context->values_[nd.a];
    }
    if (nd.b != kNoChild) {
      if (nd.b >= context->stamps_.size() ||
          context->stamps_[nd.b] != stamp)
        return false;
      b = context->values_[nd.b];
    }
    uint16_t bits = nd.bits;
    uint64_t v;
    if (stats) {
      stats->computed_nodes += 1;
      if (nd.kind == PKind::Read || nd.kind == PKind::EofRead) {
        stats->read_nodes += 1;
        stats->read_bytes += nd.kind == PKind::Read ? bits / 8 : 1;
      }
    }
    switch (nd.kind) {
      case PKind::Opaque: return false;
      case PKind::Read: {
        // Length-boundary semantics: a byte past the candidate length is a
        // missing byte and evaluates as EOF (masked -1 at the node width),
        // matching the getc-family behavior. This routes short candidates
        // from byte nodes into the EofRead/Count length nodes instead of
        // failing the eval (conservative admission).
        uint32_t nbytes = nd.bits / 8;
        if (nd.bits == 0 || nd.bits % 8 != 0 || nbytes > 8) return false;
        v = 0;
        for (uint32_t k = 0; k < nbytes; k++) {
          if (nd.value + k < len) {
            v |= (uint64_t)input[nd.value + k] << (8 * k);
          } else {
            v |= 0xFFull << (8 * k);
          }
        }
        break;
      }
      case PKind::Len: v = mask_bits(len, bits); break;
      case PKind::EofRead: {
        // getc-family read: one byte at nd.value, zero-extended; a missing
        // byte (offset >= len) is EOF (masked -1 at the node width).
        if (nd.bits == 0 || nd.bits > 64) return false;
        v = (nd.value < len) ? (uint64_t)input[nd.value] : mask_bits(~0ull, bits);
        break;
      }
      case PKind::Count:
      case PKind::CountNeg1:
      case PKind::CountElems: {
        if (nd.bits == 0 || nd.bits > 64) return false;
        uint64_t pos = nd.value;
        if (len <= pos) {
          v = (nd.kind == PKind::CountNeg1) ? mask_bits(~0ull, bits) : 0;
          break;
        }
        uint64_t avail = (uint64_t)len - pos;
        if (nd.kind == PKind::CountElems) {
          // b = item size; a = nmemb. ret is the number of complete elements.
          // fread(ptr, 0, ...) reads nothing: zero elements.
          if (b == 0) { v = 0; break; }
          uint64_t elems = avail / b;
          v = (a < elems) ? a : elems;
        } else {
          v = (a < avail) ? a : avail;
        }
        v = mask_bits(v, bits);
        break;
      }
      case PKind::Const: v = mask_bits(nd.value, bits); break;
      case PKind::Add: v = mask_bits(a + b, bits); break;
      case PKind::Sub: v = mask_bits(a - b, bits); break;
      case PKind::Mul: v = mask_bits(a * b, bits); break;
      case PKind::UDiv:
        v = (b == 0) ? mask_bits(~0ull, bits) : mask_bits(a / b, bits);
        break;
      case PKind::SDiv: {
        int64_t sa = sext_bits(a, bits), sb = sext_bits(b, bits);
        if (sb == 0) {
          v = mask_bits(sa < 0 ? 1 : (uint64_t)-1, bits);
        } else if (sb == -1) {
          v = mask_bits(0 - a, bits);
        } else {
          v = mask_bits((uint64_t)(sa / sb), bits);
        }
        break;
      }
      case PKind::URem: v = (b == 0) ? a : mask_bits(a % b, bits); break;
      case PKind::SRem: {
        int64_t sa = sext_bits(a, bits), sb = sext_bits(b, bits);
        if (sb == 0) {
          v = a;
        } else if (sb == -1) {
          v = 0;
        } else {
          v = mask_bits((uint64_t)(sa % sb), bits);
        }
        break;
      }
      case PKind::UMin: {
        uint64_t av = mask_bits(a, bits), bv = mask_bits(b, bits);
        v = av < bv ? av : bv;
        break;
      }
      case PKind::UMax: {
        uint64_t av = mask_bits(a, bits), bv = mask_bits(b, bits);
        v = av > bv ? av : bv;
        break;
      }
      case PKind::SMin:
        v = sext_bits(a, bits) < sext_bits(b, bits)
                ? mask_bits(a, bits) : mask_bits(b, bits);
        break;
      case PKind::SMax:
        v = sext_bits(a, bits) > sext_bits(b, bits)
                ? mask_bits(a, bits) : mask_bits(b, bits);
        break;
      case PKind::Neg: v = mask_bits(0 - a, bits); break;
      case PKind::Not: v = mask_bits(~a, bits); break;
      case PKind::And: v = mask_bits(a & b, bits); break;
      case PKind::Or: v = mask_bits(a | b, bits); break;
      case PKind::Xor: v = mask_bits(a ^ b, bits); break;
      case PKind::Shl: v = (b >= bits) ? 0 : mask_bits(a << b, bits); break;
      case PKind::LShr: v = (b >= bits) ? 0 : (mask_bits(a, bits) >> b); break;
      case PKind::AShr:
        v = b >= bits ? (sext_bits(a, bits) < 0 ? mask_bits(~0ull, bits) : 0)
                      : mask_bits((uint64_t)(sext_bits(a, bits) >> b), bits);
        break;
      case PKind::Ctlz: {
        uint64_t x = mask_bits(a, bits);
        if (x == 0) v = bits;
        else {
          v = 0;
          for (int i = (int)bits - 1; i >= 0 && ((x >> i) & 1) == 0; --i)
            ++v;
        }
        break;
      }
      case PKind::Cttz: {
        uint64_t x = mask_bits(a, bits);
        if (x == 0) v = bits;
        else {
          v = 0;
          while (((x >> v) & 1) == 0) ++v;
        }
        break;
      }
      case PKind::FpAdd:
      case PKind::FpSub:
      case PKind::FpMul:
      case PKind::FpDiv:
      case PKind::FpRem:
      case PKind::FpMin:
      case PKind::FpMax:
      case PKind::FpCopySign:
      case PKind::FpPow:
        if (!eval_fp_binary(nd.kind, bits, a, b, &v)) return false;
        break;
      case PKind::FpNeg:
      case PKind::FpAbs:
      case PKind::FpSqrt:
      case PKind::FpRound:
      case PKind::FpIsNan:
      case PKind::FpIsInf:
      case PKind::FpIsFinite:
      case PKind::FpSignBit:
      case PKind::FpLrint:
      case PKind::FpExp:
      case PKind::FpExp2:
      case PKind::FpLog:
      case PKind::FpLog2:
      case PKind::FpLog10:
      case PKind::FpLog1p:
        if (!eval_fp_unary(nd.kind, nd.kind == PKind::FpLrint
                                           ? nodes[nd.a].bits : bits,
                           a, nd.value, &v)) return false;
        break;
      case PKind::FpTrunc:
      case PKind::FpExt:
      case PKind::FpToUI:
      case PKind::FpToSI:
      case PKind::FpToFP:
      case PKind::FpSIToFP:
        if (!eval_fp_cast(nd.kind, bits, nodes[nd.a].bits, a, &v))
          return false;
        break;
      case PKind::ZExt: v = mask_bits(a, bits); break;
      case PKind::SExt:
        v = mask_bits((uint64_t)sext_bits(a, nodes[nd.a].bits), bits);
        break;
      case PKind::Extract:
        v = nd.value >= 64 ? 0 : mask_bits(a >> nd.value, bits);
        break;
      case PKind::Concat: {
        // Runtime __taint_union_load records l1 as the low-order part and
        // l2 as the newly appended high-order part. Keep that little-endian
        // byte assembly here: (high << low_bits) | low.
        uint16_t low_bits = nodes[nd.a].bits;
        if (low_bits >= 64) return false;
        v = mask_bits((b << low_bits) | a, bits);
        break;
      }
      case PKind::Memcmp: {
        uint32_t nbytes = static_cast<uint32_t>(nd.value);
        if (nbytes == 0 || nbytes > 8) return false;
        int64_t cmp = 0;
        for (uint32_t k = 0; k < nbytes; ++k) {
          uint8_t av = static_cast<uint8_t>(a >> (k * 8));
          uint8_t bv = static_cast<uint8_t>(b >> (k * 8));
          if (av != bv) {
            cmp = av < bv ? -1 : 1;
            break;
          }
        }
        v = mask_bits(static_cast<uint64_t>(cmp), bits);
        break;
      }
      case PKind::Equal: v = (mask_bits(a, bits) == mask_bits(b, bits)); break;
      case PKind::Distinct: v = (mask_bits(a, bits) != mask_bits(b, bits)); break;
      case PKind::Ult: v = (mask_bits(a, bits) < mask_bits(b, bits)); break;
      case PKind::Ule: v = (mask_bits(a, bits) <= mask_bits(b, bits)); break;
      case PKind::Ugt: v = (mask_bits(a, bits) > mask_bits(b, bits)); break;
      case PKind::Uge: v = (mask_bits(a, bits) >= mask_bits(b, bits)); break;
      case PKind::Slt: v = (sext_bits(a, bits) < sext_bits(b, bits)); break;
      case PKind::Sle: v = (sext_bits(a, bits) <= sext_bits(b, bits)); break;
      case PKind::Sgt: v = (sext_bits(a, bits) > sext_bits(b, bits)); break;
      case PKind::Sge: v = (sext_bits(a, bits) >= sext_bits(b, bits)); break;
      default: return false;
    }
    context->values_[frame.first] = v;
    context->stamps_[frame.first] = stamp;
  }
  if (context->stamps_[pred.root] != stamp) return false;
  *out = context->values_[pred.root];
  return true;
}

}  // namespace pcbt
