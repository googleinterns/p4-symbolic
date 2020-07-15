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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H_
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H_

#include "p4_symbolic/symbolic/symbolic.h"
#include "z3.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

// Free (unconstrained) symbolic context consisting of input symbolic variables
// for headers and empty trace and metadata.
SymbolicPerPacketState FreeSymbolicPacketState();

// Extract a concrete context by evaluating every component's corresponding
// expression on the model.
ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model);

// Merges two symbolic states into a single state. A field in the new state
// has the value of the changed state if the condition is true, and the value
// of the original one otherwise.
// If original does not contain that field, a default value (e.g. -1) is used if
// the condition is false.
// Assertion: the changed state should not remove fields.
SymbolicPerPacketState MergeStatesOnCondition(
    const SymbolicPerPacketState &original,
    const SymbolicPerPacketState &changed, const z3::expr &condition);

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_UTIL_H_
