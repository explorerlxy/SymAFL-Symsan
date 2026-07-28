#include "pred.hpp"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

using namespace __dfsan;

namespace pcbt {

namespace {
constexpr uint32_t kNoChild = UINT32_MAX;
constexpr size_t kMaxArenaNodes = 2'000'000;  // per-run cap
constexpr size_t kMaxDepth = 256;             // recursion cap -> opaque
}  // namespace

RunConverter::RunConverter(const dfsan_label_info *table, size_t table_labels)
    : table_(table), table_labels_(table_labels),
      arena_(std::make_shared<PredArena>()) {
  arena_->nodes.reserve(4096);
}

uint32_t RunConverter::add(PKind kind, uint16_t bits, uint32_t a, uint32_t b,
                           uint64_t value, uint32_t aux) {
  if (arena_->nodes.size() >= kMaxArenaNodes) {
    overflow_ = true;
    return 0;
  }
  arena_->nodes.push_back({kind, bits, a, b, value, aux});
  return (uint32_t)arena_->nodes.size() - 1;
}

uint32_t RunConverter::add_const(uint64_t value, uint16_t bits) {
  if (bits == 0 || bits > 64) { overflow_ = true; return 0; }
  return add(PKind::Const, bits, kNoChild, kNoChild, value);
}

uint32_t RunConverter::conv_child(uint32_t label, uint64_t cval,
                                  uint16_t cbits, size_t depth) {
  if (label == 0) return add_const(cval, cbits);
  return convert(label, depth + 1);
}

uint32_t RunConverter::convert(uint32_t label, size_t depth) {
  if (overflow_ || depth > kMaxDepth || label >= table_labels_ ||
      label == kInitializingLabel) {
    overflow_ = true;
    return 0;
  }
  auto it = label_map_.find(label);
  if (it != label_map_.end()) return it->second;

  const dfsan_label_info *info = &table_[label];
  uint32_t op = info->op;
  uint32_t op_lo = op & 0xff;
  uint32_t idx = 0;

  if (op == 0) {
    // raw input byte: offset in op1, input id in op2 (multi-input unused)
    idx = add(PKind::Read, 8, kNoChild, kNoChild, info->op1.i, 1);
  } else if (op_lo == Load) {
    // uload: consecutive input bytes fused into one read
    if (info->l1 == 0 || info->l1 >= table_labels_ || info->l2 == 0 ||
        info->l2 > 8) {
      overflow_ = true;
      return 0;
    }
    idx = add(PKind::Read, (uint16_t)(info->l2 * 8), kNoChild, kNoChild,
              table_[info->l1].op1.i, info->l2);
  } else {
    idx = convert_op(info, op, op_lo, depth);
  }

  if (!overflow_) label_map_.emplace(label, idx);
  return idx;
}

uint32_t RunConverter::convert_op(const dfsan_label_info *info, uint32_t op,
                                  uint32_t op_lo, size_t depth) {
  uint16_t size = info->size;
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
    uint32_t a = conv_child(info->l1, info->op1.i, 64, depth);
    return add(PKind::Extract, size, a, kNoChild, off);
  }
  if (op == __dfsan::Concat) {
    if (info->l1 == 0 && info->l2 == 0) { overflow_ = true; return 0; }
    uint16_t cbits1 = size, cbits2 = size;
    if (info->l1 == 0 && info->l2 != 0 && info->l2 < table_labels_) {
      if (table_[info->l2].size > size) { overflow_ = true; return 0; }
      cbits1 = (uint16_t)(size - table_[info->l2].size);
    }
    if (info->l2 == 0 && info->l1 != 0 && info->l1 < table_labels_) {
      if (table_[info->l1].size > size) { overflow_ = true; return 0; }
      cbits2 = (uint16_t)(size - table_[info->l1].size);
    }
    uint32_t a = conv_child(info->l1, info->op1.i, cbits1, depth);
    uint32_t b = conv_child(info->l2, info->op2.i, cbits2, depth);
    return add(PKind::Concat, size, a, b);
  }
  if (op_lo == ICmp) {
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
      default: overflow_ = true; return 0;
    }
    uint32_t a = conv_child(info->l1, info->op1.i, size, depth);
    uint32_t b = conv_child(info->l2, info->op2.i, size, depth);
    return add(kind, size, a, b);
  }
  if (unary) {
    uint32_t a = conv_child(info->l1, info->op1.i, size, depth);
    return add(kind, size, a, kNoChild);
  }
  if (binary) {
    uint32_t a = conv_child(info->l1, info->op1.i, size, depth);
    uint32_t b = conv_child(info->l2, info->op2.i, size, depth);
    return add(kind, size, a, b);
  }

  // FP ops, string ops, Arg/Free, fmemcmp, GEP artifacts, ... : unsupported
  overflow_ = true;
  return 0;
}

Predicate RunConverter::conv(uint32_t label) {
  Predicate pred;
  pred.arena = arena_;
  if (label == 0 || label >= table_labels_) {
    pred.opaque = true;
    return pred;
  }
  pred.root = convert(label, 0);
  pred.opaque = overflow_;

  // compute the subtree evaluation order (ascending arena indices; children
  // always precede parents) + the input-read set
  if (!pred.opaque) {
    std::unordered_set<uint32_t> seen;
    std::vector<uint32_t> stack = {pred.root};
    while (!stack.empty()) {
      uint32_t i = stack.back();
      stack.pop_back();
      if (!seen.insert(i).second) continue;
      const PNode &nd = arena_->nodes[i];
      if (nd.a != kNoChild) stack.push_back(nd.a);
      if (nd.b != kNoChild) stack.push_back(nd.b);
    }
    pred.order.assign(seen.begin(), seen.end());
    std::sort(pred.order.begin(), pred.order.end());
    pred.reads.reserve(8);
    for (uint32_t i : pred.order) {
      const PNode &nd = arena_->nodes[i];
      if (nd.kind == PKind::Read)
        pred.reads.emplace_back((uint32_t)nd.value, nd.aux);
    }
    std::sort(pred.reads.begin(), pred.reads.end());
    pred.reads.erase(std::unique(pred.reads.begin(), pred.reads.end()),
                     pred.reads.end());
  }
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

bool eval_predicate(const Predicate &pred, const uint8_t *input, uint32_t len,
                    uint64_t *out) {
  if (pred.opaque || !pred.arena) return false;
  const auto &nodes = pred.arena->nodes;
  const std::vector<uint32_t> &order = pred.order;
  if (order.empty()) return false;

  static thread_local std::vector<uint64_t> vals;
  if (vals.size() < nodes.size()) vals.resize(nodes.size());

  for (uint32_t i : order) {
    const PNode &nd = nodes[i];
    uint64_t a = nd.a != kNoChild ? vals[nd.a] : 0;
    uint64_t b = nd.b != kNoChild ? vals[nd.b] : 0;
    uint16_t bits = nd.bits;
    uint64_t v;
    switch (nd.kind) {
      case PKind::Opaque: return false;
      case PKind::Read: {
        if (nd.aux == 0 || nd.aux > 8 || nd.value + nd.aux > len) return false;
        v = 0;
        for (uint32_t k = 0; k < nd.aux; k++)
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
          v = mask_bits((uint64_t)-sa, bits);
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
      case PKind::AShr: {
        if (b >= bits) {
          v = (sext_bits(a, bits) < 0) ? mask_bits(~0ull, bits) : 0;
        } else {
          v = mask_bits((uint64_t)(sext_bits(a, bits) >> b), bits);
        }
        break;
      }
      case PKind::ZExt: v = mask_bits(a, bits); break;
      case PKind::SExt: {
        uint16_t from = nodes[nd.a].bits;
        v = mask_bits((uint64_t)sext_bits(a, from), bits);
        break;
      }
      case PKind::Extract: {
        v = (nd.value >= 64) ? 0 : mask_bits(a >> nd.value, bits);
        break;
      }
      case PKind::Concat: {
        uint16_t lo_bits = nodes[nd.b].bits;
        if (lo_bits >= 64) return false;
        v = mask_bits((a << lo_bits) | b, bits);
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
    vals[i] = v;
  }
  *out = vals[pred.root];
  return true;
}

}  // namespace pcbt
