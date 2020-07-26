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

// Defines our wrapper for typed symbolic expression.

#ifndef P4_SYMBOLIC_SYMBOLIC_TYPED_H_
#define P4_SYMBOLIC_SYMBOLIC_TYPED_H_

#include "gutil/status.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// This is very similar to z3::expr, however it stores additional type
// information (e.g. sign), and performs type checking on copy/assignment,
// and can unify different sized bit vectors by padding.
//
// Specifically, when a typed expression is declared, it can only be re-assigned
// to z3::expr of the same matching sort (or of a bit vector sort that can be
// padded to that sort).
//
// This is important for metadata fields, which may be assigned new values as
// the symbolic program is evaluated.
//
// Additionally, this class overrides operators, similar to z3::expr, with
// additional type checking (for signedness) and padding when needed.
class TypedExpr {
 private:
  // The underlying symbolic expression that is the current value of this
  // typed expression.
  z3::expr expr_;
  // The declared sort of this typed expression. It will only accept
  // reassignments to expressions of this same sort.
  // Guaranteed to match the sort of expr_.
  z3::sort sort_;
  // Only relevant if sort_ is a bitvector. Specifies whether the bitvector
  // is interpreted as signed (i.e. int<n> in P4) or unsigned (i.e. bit<n>
  // in P4).
  // Z3 does not make a distinction between these two cases at the sort level,
  // instead, it exposed two sets of operations on bit vectors, corresponding
  // to either cases.
  // This class chooses which operation to apply based on this bool value.
  bool signed_;

 public:
  explicit TypedExpr(z3::expr expr)
      : expr_(expr), sort_(expr.get_sort()), signed_(false) {}
  explicit TypedExpr(z3::expr expr, bool sign)
      : expr_(expr), sort_(expr.get_sort()), signed_(sign) {}

  // Copyable and Movable when creating new instances.
  TypedExpr(const TypedExpr &other) = default;
  TypedExpr(TypedExpr &&other) = default;

  // Can be re-assigned (via copy or move) as long as the re-assignment respects
  // the declared sort.
  TypedExpr &operator=(const TypedExpr &other);
  TypedExpr &operator=(TypedExpr &&other);

  // Accessors
  const z3::expr &expr() const { return this->expr_; }
  const z3::sort &sort() const { return this->sort_; }
  bool is_signed() const { return this->signed_; }
  std::string to_string() const { return this->expr_.to_string(); }

  // Overloaded operators exposing corresponding z3::expr operators after sort
  // checking and padding.
  TypedExpr operator==(const TypedExpr &b) const;
  TypedExpr operator&&(const TypedExpr &b) const;
  TypedExpr operator||(const TypedExpr &b) const;
  TypedExpr operator!() const;

  // If-then-else.
  static TypedExpr ite(const TypedExpr &condition, const TypedExpr &true_,
                       const TypedExpr &false_);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_TYPED_H_
