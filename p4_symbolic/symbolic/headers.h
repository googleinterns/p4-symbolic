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

// Contains helpers for creating, extracting, and managing concerete and
// symbolic header structs.

#ifndef P4_SYMBOLIC_SYMBOLIC_HEADERS_H_
#define P4_SYMBOLIC_SYMBOLIC_HEADERS_H_

#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace headers {

// Free (unconstrained) symbolic header.
SymbolicHeader FreeSymbolicHeader();

// Extract a concrete header by evaluating every field's corresponding
// expression in the model.
ConcreteHeader ExtractConcreteHeaders(SymbolicHeader header, z3::model model);

// Merges two symbolic headers into a single header. A field in the new header
// has the value of the changed state if the condition is true, and the value
// of the original one otherwise.
SymbolicHeader MergeHeadersOnCondition(const SymbolicHeader &original,
                                       const SymbolicHeader &changed,
                                       const TypedExpr &condition);

}  // namespace headers
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_HEADERS_H_
