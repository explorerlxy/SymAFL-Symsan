#include "pred.hpp"

#include <algorithm>
#include <functional>
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
      fail(PredError::InvalidWidth);
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
  if (op == __dfsan::Extract || op_lo == Trunc ||
      op_lo == Neg || op_lo == Not || op_lo == ZExt || op_lo == SExt)
    return 1;
  if (op == __dfsan::Concat || is_fmemcmp(op) || op_lo == ICmp ||
      op_lo == FCmp || op_lo == Add || op_lo == Sub || op_lo == Mul ||
      op_lo == UDiv || op_lo == SDiv || op_lo == URem || op_lo == SRem ||
      op_lo == Shl || op_lo == LShr || op_lo == AShr || op_lo == And ||
      op_lo == Or || op_lo == Xor)
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
      if (count == 2 && info->l2 != 0) stack.push_back({info->l2, false});
      if (count >= 1 && info->l1 != 0) stack.push_back({info->l1, false});
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
      idx = convert_op(info, op, op_lo);
    }
    if (idx == kInvalidNode) break;
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

uint32_t RunConverter::convert_op(const dfsan_label_info *info, uint32_t op,
                                  uint32_t op_lo) {
  // fmemcmp's size is a byte count, unlike ordinary label widths.  The DFSan
  // runtime copies up to eight concrete bytes into op1/op2, so this scalar
  // PCBT grammar can model exactly the byte range it records.  Its canonical
  // -1/0/+1 result preserves every comparison against zero (the only admitted
  // use; target preflight rejects other fmemcmp-derived predicates).
  if (is_fmemcmp(static_cast<uint16_t>(op))) {
    if (info->size == 0 || info->size > 8) {
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
  PKind kind;
  bool unary = false, binary = false;

  switch (op_lo) {
    case Add: kind = PKind::Add; binary = true; break;
    case Sub: kind = PKind::Sub; binary = true; break;
    case Mul: kind = PKind::Mul; binary = true; break;
    case UDiv: kind = PKind::UDiv; binary = true; break;
    case SDiv: kind = PKind::SDiv; binary = true; break;
    case URem: kind = PKind::URem; binary = true; break;
    case SRem: kind = PKind::SRem; binary = true; break;
    case Shl: kind = PKind::Shl; binary = true; break;
    case LShr: kind = PKind::LShr; binary = true; break;
    case AShr: kind = PKind::AShr; binary = true; break;
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
    uint64_t off = (op == __dfsan::Extract) ? info->op2.i : 0;
    uint32_t a = conv_child(info->l1, info->op1.i, 64);
    return a == kInvalidNode ? kInvalidNode
                             : add(PKind::Extract, size, a, kNoChild, off);
  }
  if (op == __dfsan::Concat) {
    if (info->l1 == 0 && info->l2 == 0) {
      fail(PredError::BadConcat);
      return kInvalidNode;
    }
    uint16_t cbits1 = size, cbits2 = size;
    if (info->l1 == 0 && info->l2 != 0 && info->l2 < table_labels_) {
      if (table_[info->l2].size > size) {
        fail(PredError::BadConcat);
        return kInvalidNode;
      }
      cbits1 = (uint16_t)(size - table_[info->l2].size);
    }
    if (info->l2 == 0 && info->l1 != 0 && info->l1 < table_labels_) {
      if (table_[info->l1].size > size) {
        fail(PredError::BadConcat);
        return kInvalidNode;
      }
      cbits2 = (uint16_t)(size - table_[info->l1].size);
    }
    uint32_t a = conv_child(info->l1, info->op1.i, cbits1);
    uint32_t b = conv_child(info->l2, info->op2.i, cbits2);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(PKind::Concat, size, a, b);
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
      uint32_t count = build_flen_count(table_[info->l1], size, other);
      if (count == kInvalidNode || other == kInvalidNode) return kInvalidNode;
      return add(kind, size, count, other);
    }
    if (right_flen && !left_flen && info->l1 != 0) {
      uint32_t other = conv_child(info->l1, info->op1.i, size);
      uint32_t count = build_flen_count(table_[info->l2], size, other);
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
    uint32_t a = conv_child(info->l1, info->op1.i, size);
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
bool RunConverter::string_bytes(dfsan_label content, size_t max_bytes,
                                std::vector<StringByte> &out) {
  std::vector<uint64_t> offs;
  if (!collect_byte_offsets(content, max_bytes, offs)) return false;
  if (offs.empty() || offs.size() > max_bytes) return false;
  std::sort(offs.begin(), offs.end());
  for (size_t i = 0; i < offs.size(); ++i) {
    if (i > 0 && offs[i] != offs[i - 1] + 1) return false;
    uint32_t nd = add(PKind::Read, 8, kNoChild, kNoChild, offs[i]);
    if (nd == kInvalidNode) return false;
    out.push_back({nd, (uint32_t)offs[i]});
  }
  return true;
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

namespace {
inline uint64_t mask_bits(uint64_t v, uint16_t bits) {
  return bits >= 64 ? v : (v & ((1ull << bits) - 1));
}
inline int64_t sext_bits(uint64_t v, uint16_t bits) {
  if (bits >= 64) return (int64_t)v;
  uint64_t m = 1ull << (bits - 1);
  return (int64_t)((v ^ m) - m);
}
}  // namespace

bool eval_predicate(const PredArena &arena, const Predicate &pred,
                    const uint8_t *input, uint32_t len, uint64_t *out,
                    EvalContext *context) {
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
    if (context->stamps_[frame.first] == stamp) continue;
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
      case PKind::ZExt: v = mask_bits(a, bits); break;
      case PKind::SExt:
        v = mask_bits((uint64_t)sext_bits(a, nodes[nd.a].bits), bits);
        break;
      case PKind::Extract:
        v = nd.value >= 64 ? 0 : mask_bits(a >> nd.value, bits);
        break;
      case PKind::Concat: {
        uint16_t lo_bits = nodes[nd.b].bits;
        if (lo_bits >= 64) return false;
        v = mask_bits((a << lo_bits) | b, bits);
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
