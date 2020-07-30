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

// Defines a wrapper around z3 c++ API operators.
// The wrappers ensure sort compatibility, and pad bitvectors when needed.
// Additionally, they use absl::Status to convey sort compatibility failures
// instead of runtime crashes.

#include "p4_symbolic/symbolic/operators.h"

#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {
namespace symbolic {
namespace operators {

// Pads bitvector with padsize-many zero bits
// will fail with a runtime error if bitvector is not of bv sort, use after
// checking that the sort is correct.
z3::expr Pad(const z3::expr &bitvector, int pad_size) {
  if (pad_size > 0) {
    return z3::concat(Z3Context().bv_val(0, pad_size), bitvector);
  }
  return bitvector;
}

// Check that the two expressions have compatible sorts, and return an
// absl error otherwise.
// If the expressions are bitvector, the shortest will be padded to match
// the longest.
gutil::StatusOr<std::pair<z3::expr, z3::expr>> SortCheckAndPad(
    const z3::expr &a, const z3::expr &b) {
  // Totally incompatible sorts (e.g. int and bitvector).
  if (a.get_sort().sort_kind() != b.get_sort().sort_kind()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Incompatible sorts \"", a.get_sort().to_string(),
                     "\" and \"", b.get_sort().to_string(), "\""));
  }
  // If bit vectors, pad to the largest size.
  if (a.get_sort().is_bv()) {
    int a_len = a.get_sort().bv_size();
    int b_len = b.get_sort().bv_size();
    return std::make_pair(Pad(a, b_len - a_len), Pad(b, a_len - b_len));
  }
  return std::make_pair(z3::expr(a), z3::expr(b));
}

gutil::StatusOr<z3::expr> Plus(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr + b_expr;
}
gutil::StatusOr<z3::expr> Minus(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr - b_expr;
}
gutil::StatusOr<z3::expr> Times(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr * b_expr;
}
gutil::StatusOr<z3::expr> Eq(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr == b_expr;
}
gutil::StatusOr<z3::expr> Neq(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr != b_expr;
}
gutil::StatusOr<z3::expr> Lt(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return z3::ult(a_expr, b_expr);
}
gutil::StatusOr<z3::expr> Lte(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return z3::ule(a_expr, b_expr);
}
gutil::StatusOr<z3::expr> Gt(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return z3::ugt(a_expr, b_expr);
}
gutil::StatusOr<z3::expr> Gte(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return z3::uge(a_expr, b_expr);
}
gutil::StatusOr<z3::expr> Not(const z3::expr &a) { return !a; }
gutil::StatusOr<z3::expr> And(const z3::expr &a, const z3::expr &b) {
  return a && b;
}
gutil::StatusOr<z3::expr> Or(const z3::expr &a, const z3::expr &b) {
  return a || b;
}
gutil::StatusOr<z3::expr> BitNeg(const z3::expr &a) { return ~a; }
gutil::StatusOr<z3::expr> BitAnd(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr & b_expr;
}
gutil::StatusOr<z3::expr> BitOr(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr | b_expr;
}
gutil::StatusOr<z3::expr> BitXor(const z3::expr &a, const z3::expr &b) {
  ASSIGN_OR_RETURN(auto pair,
                   p4_symbolic::symbolic::operators::SortCheckAndPad(a, b));
  auto [a_expr, b_expr] = pair;
  return a_expr ^ b_expr;
}
gutil::StatusOr<z3::expr> LShift(const z3::expr &bits, const z3::expr &shift) {
  return z3::shl(bits, shift);
}
gutil::StatusOr<z3::expr> RShift(const z3::expr &bits, const z3::expr &shift) {
  return z3::lshr(bits, shift);
}

// If then else.
gutil::StatusOr<z3::expr> Ite(const z3::expr &condition,
                              const z3::expr &true_value,
                              const z3::expr &false_value) {
  // Optimization: if both branches are the same *syntactically*
  // then we can just use the branch expression directly and no need
  // for an if-then-else statement.
  if (z3::eq(true_value, false_value)) {
    return true_value;
  }

  // Values in both cases must have the same sort and signedness.
  ASSIGN_OR_RETURN(auto pair, SortCheckAndPad(true_value, false_value));
  auto [a_expr, b_expr] = pair;
  return z3::ite(condition, a_expr, b_expr);
}

// Conversions.
gutil::StatusOr<z3::expr> ToBoolSort(const z3::expr &a) {
  if (a.get_sort().is_bool()) {
    return a;
  } else if (a.get_sort().is_bv()) {
    return Gte(a, Z3Context().bv_val(1, 1));
  } else if (a.get_sort().is_int()) {
    return a >= Z3Context().int_val(1);
  } else {
    return absl::InvalidArgumentError("Illegal conversion to bool sort");
  }
}
gutil::StatusOr<z3::expr> ToBitVectorSort(const z3::expr &a,
                                          unsigned int size) {
  if (a.get_sort().is_bool()) {
    z3::expr bits =
        z3::ite(a, Z3Context().bv_val(1, 1), Z3Context().bv_val(0, 1));
    return Pad(bits, size - 1);
  } else if (a.get_sort().is_bv()) {
    if (a.get_sort().bv_size() <= size) {
      return Pad(a, size - a.get_sort().bv_size());
    }
  }
  return absl::InvalidArgumentError("Illegal conversion to bitvector sort");
}

// Prefix equality.
gutil::StatusOr<z3::expr> PrefixEq(const z3::expr &a, const z3::expr &b,
                                   unsigned int prefix_size) {
  if (!a.get_sort().is_bv() || !b.get_sort().is_bv()) {
    return absl::InvalidArgumentError("PrefixEq is only valid for bitvectors");
  }

  unsigned int a_size = a.get_sort().bv_size();
  unsigned int b_size = b.get_sort().bv_size();
  z3::expr a_expr = a;
  z3::expr b_expr = b;

  // Pad short bit vectors to be at least as large as the prefix to extract.
  if (a_size < prefix_size) {
    a_expr = Pad(a, prefix_size - a_size);
    a_size = prefix_size;
  }
  if (b_size < prefix_size) {
    b_expr = Pad(b, prefix_size - b_size);
    b_size = prefix_size;
  }

  // Extract prefix from bit vectors.
  if (a_size > prefix_size) {
    // Note: extract(hi, lo) is inclusive on both ends.
    a_expr = a_expr.extract(a_size - 1, a_size - prefix_size);
  }
  if (b_size > prefix_size) {
    b_expr = b_expr.extract(b_size - 1, b_size - prefix_size);
  }

  return a_expr == b_expr;
}

}  // namespace operators
}  // namespace symbolic
}  // namespace p4_symbolic
