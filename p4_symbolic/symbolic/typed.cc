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

// Pad if needed by using the appropriate z3 API.
#define PAD(bitvector, pad_size)                                               \
  pad_size > 0 ? z3::concat(Z3Context().bv_val(0, pad_size), bitvector.expr()) \
               : bitvector.expr()

// This macro is used through out the implementation of the overloaded
// operators for the TypedExpr class.
// It sort checks the two operands a and b, and if they were bit vectors,
// it will perform any needed size padding.
// The macro will define two z3::expr variables "a_expr" and "b_expr",
// corresponding to the finalized expressions of the two operands.
#define SORT_CHECK_AND_PAD(a, b)                        \
  z3::expr a_expr = a.expr_;                            \
  z3::expr b_expr = b.expr_;                            \
  assert(a.sort().sort_kind() == b.sort().sort_kind()); \
  if (a.sort().is_bv()) {                               \
    int a_len = a.sort().bv_size();                     \
    int b_len = b.sort().bv_size();                     \
    a_expr = PAD(a, b_len - a_len);                     \
    b_expr = PAD(b, a_len - b_len);                     \
  }

namespace p4_symbolic {
namespace symbolic {

// Copy and move assignment operators must respect pre-declared sort.
TypedExpr &TypedExpr::operator=(const TypedExpr &other) {
  assert(this->sort().sort_kind() == other.sort().sort_kind());
  if (this->sort().is_bv()) {
    // We can only re-assign bit vectors to ones of equal or larger size.
    unsigned int size_diff = this->sort().bv_size() - other.sort().bv_size();
    assert(size_diff >= 0);
    // All is good, copy other to this padding it to the proper bit length.
    this->expr_ = PAD(other, size_diff);
  } else {
    // For other sorts, we are all good and can assign directly.
    this->expr_ = other.expr_;
  }

  return *this;
}
TypedExpr &TypedExpr::operator=(TypedExpr &&other) {
  assert(this->sort().sort_kind() == other.sort().sort_kind());
  if (this->sort().is_bv()) {
    unsigned int size_diff = this->sort().bv_size() - other.sort().bv_size();
    assert(size_diff >= 0);
    this->expr_ = std::move(PAD(other, size_diff));
  } else {
    this->expr_ = std::move(other.expr_);
  }
  return *this;
}

// Overloaded operators.
// Arithmetic operators.
TypedExpr TypedExpr::operator+(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr + b_expr);
}
TypedExpr TypedExpr::operator-(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr - b_expr);
}
TypedExpr TypedExpr::operator*(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr * b_expr);
}

// Relational operators.
TypedExpr TypedExpr::operator==(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr == b_expr);
}
TypedExpr TypedExpr::operator!=(const TypedExpr &b) const {
  return !(*this == b);
}
TypedExpr TypedExpr::operator<(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(z3::ult(a_expr, b_expr));
}
TypedExpr TypedExpr::operator<=(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(z3::ule(a_expr, b_expr));
}
TypedExpr TypedExpr::operator>(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(z3::ugt(a_expr, b_expr));
}
TypedExpr TypedExpr::operator>=(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(z3::uge(a_expr, b_expr));
}

// Boolean operators.
TypedExpr TypedExpr::operator!() const { return TypedExpr(!this->expr_); }
TypedExpr TypedExpr::operator&&(const TypedExpr &b) const {
  return TypedExpr(this->expr_ && b.expr_);
}
TypedExpr TypedExpr::operator||(const TypedExpr &b) const {
  return TypedExpr(this->expr_ || b.expr_);
}

// Binary operators.
TypedExpr TypedExpr::operator~() const { return TypedExpr(~this->expr_); }
TypedExpr TypedExpr::operator&(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr & b_expr);
}
TypedExpr TypedExpr::operator|(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr | b_expr);
}
TypedExpr TypedExpr::operator^(const TypedExpr &b) const {
  SORT_CHECK_AND_PAD((*this), b);
  return TypedExpr(a_expr ^ b_expr);
}

// If-then-else.
TypedExpr TypedExpr::ite(const TypedExpr &condition,
                         const TypedExpr &true_value,
                         const TypedExpr &false_value) {
  // Optimization: if both branches are the same *syntactically*
  // then we can just use the branch expression directly and no need
  // for an if-then-else statement.
  if (z3::eq(true_value.expr(), false_value.expr())) {
    return true_value;
  }

  // Values in both cases must have the same sort and signedness.
  SORT_CHECK_AND_PAD(true_value, false_value);
  return TypedExpr(z3::ite(condition.expr_, a_expr, b_expr));
}

// Bit-wise shifts
TypedExpr TypedExpr::shl(const TypedExpr &bit_vector,
                         const TypedExpr &shift_value) {
  return TypedExpr(z3::shl(bit_vector.expr_, shift_value.expr_));
}
TypedExpr TypedExpr::shr(const TypedExpr &bit_vector,
                         const TypedExpr &shift_value) {
  return TypedExpr(z3::lshr(bit_vector.expr_, shift_value.expr_));
}

}  // namespace symbolic
}  // namespace p4_symbolic
