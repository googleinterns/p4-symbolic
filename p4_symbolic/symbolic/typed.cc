// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "p4_symbolic/symbolic/typed.h"

#include <utility>

#include "p4_symbolic/symbolic/symbolic.h"

// This macro is used through out the implementation of the overloaded
// operators for the TypedExpr class.
// It sort checks the two operands a and b, and if they were bit vectors,
// it will perform any needed sign conversions and size padding.
// The macro will define two z3::expr variables "a_expr" and "b_expr",
// corresponding to the finalized expressions of the two operands.
//
// If one operand is signed and the other is not, we will need to
// make the unsigned one signed, by padding with a single
// zero bit, since the unsigned expression must be positive.
// We cannot guarantee that the original unsigned expression does
// not start with a 1 bit.
//
// As an optimization, we do not need to do that padding
// explicitly, instead we only logically account for it
// increasing the size by 1, and then the later "Pad" call
// will do that sign conversion for us along the way.
#define SORT_CHECK_AND_PADD(a, b)                          \
  z3::expr a_expr = a.expr_;                               \
  z3::expr b_expr = b.expr_;                               \
  assert(a.sort_.sort_kind() == b.sort_.sort_kind());      \
  if (a.sort_.is_bv()) {                                   \
    unsigned int a_len = a.sort_.bv_size();                \
    unsigned int b_len = b.sort_.bv_size();                \
    if (a.signed_ && !b.signed_)                           \
      b_len += 1;                                          \
    else if (!a.signed_ && b.signed_)                      \
      a_len += 1;                                          \
    unsigned int pad_size = a_len > b_len ? a_len : b_len; \
    a_expr = Pad(a, pad_size);                             \
    b_expr = Pad(b, pad_size);                             \
  }

namespace p4_symbolic {
namespace symbolic {

namespace {

z3::expr Pad(const TypedExpr &e, unsigned int size) {
  // We should determine what kind of pad we need and apply it.
  unsigned int diff = size - e.sort().bv_size();
  if (diff == 0) {
    // No padding or sign conversions needed.
    return e.expr();
  } else if (e.is_signed()) {
    // We must pad, without damaging the sign bit.
    assert(e.sort().bv_size() > 1);
    unsigned sign_bit_index = e.sort().bv_size() - 1;
    z3::expr sign_bit = e.expr().extract(sign_bit_index, sign_bit_index);
    z3::expr zeros = Z3Context().bv_val(0, diff);
    z3::expr unsign_expr = e.expr().extract(sign_bit_index - 1, 0);
    return z3::concat(z3::concat(sign_bit, zeros), unsign_expr);
  } else {
    // We must pad, but no sign issues.
    return z3::concat(Z3Context().bv_val(0, diff), e.expr());
  }
}

}  // namespace

// Copy and move assignment operators must respect pre-declared sort.
TypedExpr &TypedExpr::operator=(const TypedExpr &other) {
  assert(this->sort_.sort_kind() == other.sort_.sort_kind());
  if (this->sort_.is_bv()) {
    // We can assign an unsigned bit vector to a signed one, but not the other
    // way around.
    assert(this->signed_ || !other.signed_);
    // We can only re-assign bit vectors to ones of equal or smaller size.
    assert(this->sort_.bv_size() >= other.sort_.bv_size());
    // Finally, if assigning an unsigned bitvector to a signed one, the size
    // of the unsigned one has to be smaller than the signed one. Otherwise,
    // there is no guarantee that the unsigned value interpretation will
    // remain the same (e.g. if its most significant bit is 1).
    if (this->signed_ && !other.signed_) {
      assert(this->sort_.bv_size() > other.sort_.bv_size());
    }
    // All is good, copy other to this padding it to the proper bit length.
    this->expr_ = Pad(other, this->sort_.bv_size());
  } else {
    // For other sorts, we are all good and can assign directly.
    this->expr_ = other.expr_;
  }
  return *this;
}
TypedExpr &TypedExpr::operator=(TypedExpr &&other) {
  // Same sort-checking assertions as copy assignment.
  assert(this->sort_.sort_kind() == other.sort_.sort_kind());
  if (this->sort_.is_bv()) {
    assert(this->signed_ || !other.signed_);
    assert(this->sort_.bv_size() >= other.sort_.bv_size());
    if (this->signed_ && !other.signed_) {
      assert(this->sort_.bv_size() > other.sort_.bv_size());
    }
    this->expr_ = std::move(Pad(other, this->sort_.bv_size()));
  } else {
    this->expr_ = std::move(other.expr_);
  }
  return *this;
}

// Overloaded operators.
TypedExpr TypedExpr::operator==(const TypedExpr &b) const {
  SORT_CHECK_AND_PADD((*this), b);
  return TypedExpr(a_expr == b_expr, this->signed_ || b.signed_);
}
TypedExpr TypedExpr::operator&&(const TypedExpr &b) const {
  return TypedExpr(this->expr_ && b.expr_);
}
TypedExpr TypedExpr::operator||(const TypedExpr &b) const {
  return TypedExpr(this->expr_ || b.expr_);
}
TypedExpr TypedExpr::operator!() const { return TypedExpr(!this->expr_); }

// If-then-else.
TypedExpr TypedExpr::ite(const TypedExpr &condition, const TypedExpr &true_,
                         const TypedExpr &false_) {
  // Values in both cases must have the same sort and signedness.
  SORT_CHECK_AND_PADD(true_, false_);
  return TypedExpr(z3::ite(condition.expr_, a_expr, b_expr),
                   true_.signed_ || false_.signed_);
}

}  // namespace symbolic
}  // namespace p4_symbolic
