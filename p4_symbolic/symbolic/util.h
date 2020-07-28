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

// Helpful utilities for managing symbolic and concrete states.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H_
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H_

#include <string>

#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/typed.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

// Free (unconstrained) symbolic context consisting of input symbolic variables
// for headers and empty trace and metadata.
gutil::StatusOr<SymbolicPerPacketState> FreeSymbolicPacketState(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers);

// Extract a concrete context by evaluating every component's corresponding
// expression in the model.
ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model);

// Essentially a symbolic ternary choice/condition.
TypedExpr MergeExpressionsWithCondition(const TypedExpr &original,
                                        const TypedExpr &changed,
                                        const TypedExpr &condition);

// Merges two symbolic states into a single state. A field in the new state
// has the value of the changed state if the condition is true, and the value
// of the original one otherwise.
// If original does not contain that field, a default value (e.g. -1) is used if
// the condition is false.
// Assertion: the changed state should not remove fields.
SymbolicPerPacketState MergeStatesOnCondition(
    const SymbolicPerPacketState &original,
    const SymbolicPerPacketState &changed, const TypedExpr &condition);

// Transforms a value read from a TableEntry to a z3::expr.
gutil::StatusOr<TypedExpr> IrValueToZ3Expr(const pdpi::IrValue &value);

// Transforms a string value from bmv2 json to a pdpi::IrValue
gutil::StatusOr<pdpi::IrValue> StringToIrValue(std::string value);

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_UTIL_H_
