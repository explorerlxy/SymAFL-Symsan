#include "pred.hpp"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

using namespace __dfsan;

namespace pcbt {

namespace {
constexpr uint32_t kNoChild = UINT32_MAX;
constexpr uint32_t kInvalidNode = UINT32_MAX;
constexpr size_t kMaxPredicateNodes = 2'000'000;

struct ConvertFrame {
  uint32_t label;
  bool expanded;
};
}  // namespace

void EvalContext::Reset() {
  values_.clear();
  stack_.clear();
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
      op_lo == Add || op_lo == Sub || op_lo == Mul || op_lo == UDiv ||
      op_lo == SDiv || op_lo == URem || op_lo == SRem || op_lo == Shl ||
      op_lo == LShr || op_lo == AShr || op_lo == And || op_lo == Or ||
      op_lo == Xor)
    return 2;
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
    uint32_t a = conv_child(info->l1, info->op1.i, size);
    uint32_t b = conv_child(info->l2, info->op2.i, size);
    return a == kInvalidNode || b == kInvalidNode
               ? kInvalidNode : add(kind, size, a, b);
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

  // FP ops, string ops, Arg/Free, fmemcmp, GEP artifacts, ... : unsupported
  fail(PredError::UnsupportedOp, static_cast<uint16_t>(op));
  return kInvalidNode;
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
  context->stack_.push_back({pred.root, false});

  while (!context->stack_.empty()) {
    auto frame = context->stack_.back();
    context->stack_.pop_back();
    if (context->values_.find(frame.first) != context->values_.end()) continue;
    if (frame.first >= nodes.size()) return false;
    const PNode &nd = nodes[frame.first];
    if (!frame.second) {
      context->stack_.push_back({frame.first, true});
      if (nd.b != kNoChild) context->stack_.push_back({nd.b, false});
      if (nd.a != kNoChild) context->stack_.push_back({nd.a, false});
      continue;
    }

    uint64_t a = 0, b = 0;
    if (nd.a != kNoChild) {
      auto it = context->values_.find(nd.a);
      if (it == context->values_.end()) return false;
      a = it->second;
    }
    if (nd.b != kNoChild) {
      auto it = context->values_.find(nd.b);
      if (it == context->values_.end()) return false;
      b = it->second;
    }
    uint16_t bits = nd.bits;
    uint64_t v;
    switch (nd.kind) {
      case PKind::Opaque: return false;
      case PKind::Read: {
        uint32_t nbytes = nd.bits / 8;
        if (nd.bits == 0 || nd.bits % 8 != 0 || nbytes > 8 ||
            nd.value + nbytes > len) return false;
        v = 0;
        for (uint32_t k = 0; k < nbytes; k++)
          v |= (uint64_t)input[nd.value + k] << (8 * k);
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
    context->values_.emplace(frame.first, v);
  }
  auto root = context->values_.find(pred.root);
  if (root == context->values_.end()) return false;
  *out = root->second;
  return true;
}

}  // namespace pcbt
