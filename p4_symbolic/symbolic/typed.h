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

#include <string>

#include "gutil/status.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// This class is very similar to z3::expr. However, it enforces an important
// invariant: copy/move assignments to variables, map locations, etc containing
// instances of this type must maintain that the expression sort is the same.
//
// The sort of the expression includes its base type (e.g. boolean, integer,
// bitvector), as well as size information (e.g. the size of the bitvector).
//
// Example:
// // A metadata map from field names to expressions is defined at the begining.
// map<std::string, TypedExpr> metadata;
// // The map is filled with some initial mapping.
// metadata.insert({"x", TypedExpr(<bit vector of size 10>)});
// // The map is now passed to some complicated pipeline that evaluates code
// // and makes changes to the metadata map.
// // At some point this line is executed.
// metadata.at("x") = TypedExpr(<bit vector of size n>);
//
// // This above line will complete successfuly if n <= 10, it will padd
// // the assigned values with 0 bits so that the new size is 10.
// // However, if n > 10, or if the sort of the expression is not a bitvector
// // to begin with. The call will fail because of an assertion failure.
// End of Example.
//
// The class override needed operators by our symbolic code, in a way identical
// to how z3::expr overrides them, with the exception of being able to operate
// on bitvectors of different sizes via padding.
// Example:
// // This errors out:
// z3::expr<bit vector of size 5> + z3::expr<bit vector of size 4>;
// // This does not error out. The second vector is padded to 5:
// TypedExpr<bit vector of size 5> + TypedExpr<bit vector of size 4>;
//
// These operators do not violate the stated invariant, they do not mutate
// the operands. Assigning the result of an such operation to an existing
// TypedExpr must satisfiy the invariant, other wise that assignment (not the
// operator) will fail.
//
// Note about sign:
//
// We do not support signed bitvectors in this pipeline because they are not
// used in programs we are interested in.
//
// However, if the need arise to support them. The sign of bit vectors msut be
// explicitly stored in this class, because z3::expr does not store it at all.
// We recommend that the sign is stored in this class, and included in the
// invariant, so that the sign is preserved.
//
// This means that unsigned expressions may be assigned to signed ones, but not
// the other way around. Unsigned expressions must have size < than the signed
// one. Otherwise, the unsigned expression may begin with 1, and re-interpreting
// it as signed will change its value. If the size is less, the unsigned
// expression can be padded with zeros to ensure its signed interpretation
// is ok.
//
// Finally, z3 provides different implementations for the corresponding signed
// and unsigned mathematical operators, for those where the sign makes a
// difference. For example, + and - have a single implementation for both.
// While comparisons are different. z3::expr < z3::expr refers to the signed
// version, while z3::ult(<z3::expr>, <z3::expr>) refers to the unsigned
// version.
//
// We suggest that operators overloaded in this class check the sign and call
// the appropriate Z3 operations. The overloaded operators may also padd
// unsigned expressions to signed ones, so that it can operate on operands of
// different signedness.

class TypedExpr {
 private:
  // The underlying symbolic expression that is the current value of this
  // typed expression.
  // Invariant: the sort of the expression this instance is initially defined by
  // is always respected, all future assignments to it must satisify that sort.
  z3::expr expr_;

 public:
  explicit TypedExpr(z3::expr expr) : expr_(expr) {}

  // Copyable and Movable when creating new instances.
  TypedExpr(const TypedExpr &other) = default;
  TypedExpr(TypedExpr &&other) = default;

  // Can be re-assigned (via copy or move) as long as the re-assignment respects
  // the declared sort.
  TypedExpr &operator=(const TypedExpr &other);
  TypedExpr &operator=(TypedExpr &&other);

  // Accessors
  const z3::expr &expr() const { return this->expr_; }
  inline z3::sort sort() const { return this->expr_.get_sort(); }
  std::string to_string() const { return this->expr_.to_string(); }

  // Overloaded operators exposing corresponding z3::expr operators after sort
  // checking and padding.
  // Arithmetic operators.
  TypedExpr operator+(const TypedExpr &b) const;
  TypedExpr operator-(const TypedExpr &b) const;
  TypedExpr operator*(const TypedExpr &b) const;

  // Relational operators.
  TypedExpr operator==(const TypedExpr &b) const;
  TypedExpr operator!=(const TypedExpr &b) const;
  TypedExpr operator<(const TypedExpr &b) const;
  TypedExpr operator<=(const TypedExpr &b) const;
  TypedExpr operator>(const TypedExpr &b) const;
  TypedExpr operator>=(const TypedExpr &b) const;

  // Boolean operators.
  TypedExpr operator!() const;
  TypedExpr operator&&(const TypedExpr &b) const;
  TypedExpr operator||(const TypedExpr &b) const;

  // Binary operators.
  TypedExpr operator~() const;
  TypedExpr operator&(const TypedExpr &b) const;
  TypedExpr operator|(const TypedExpr &b) const;
  TypedExpr operator^(const TypedExpr &b) const;

  // If-then-else.
  static TypedExpr ite(const TypedExpr &condition, const TypedExpr &true_value,
                       const TypedExpr &false_value);
  // Bit-wise shifts
  static TypedExpr shl(const TypedExpr &bit_vector,
                       const TypedExpr &shift_value);
  static TypedExpr shr(const TypedExpr &bit_vector,
                       const TypedExpr &shift_value);

  // Converts the expression into a semantically equivalent boolean expression.
  gutil::StatusOr<TypedExpr> ToBoolSort();
  gutil::StatusOr<TypedExpr> ToBitVectorSort(unsigned int size);

  // Prefix equality: this is the basis for evaluating LPMs.
  static gutil::StatusOr<TypedExpr> PrefixEq(const TypedExpr &a,
                                             const TypedExpr &b,
                                             unsigned int prefix_size);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_TYPED_H_
