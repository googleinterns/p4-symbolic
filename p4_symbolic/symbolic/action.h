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

// Contains functions used to symbolically analyze/interprate actions
// and their bodies.
// An action is represented as a boolean symbolic z3 expression over
// unconstrained symbolic parameters corresponding to its actual P4 parameters.

#ifndef P4_SYMBOLIC_SYMBOLIC_ACTION_H_
#define P4_SYMBOLIC_SYMBOLIC_ACTION_H_

#include <string>
#include <unordered_map>
#include <vector>

#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

// Symbolically runs the given action on the given symbolic parameters.
// This produces a symbolic expression on the symbolic parameters that is
// semantically equivalent to the behavior of the action on its concrete
// parameters.
pdpi::StatusOr<SymbolicState> RunAction(
    const ir::Action &action, const std::vector<z3::expr> &symbolic_parameters,
    const SymbolicState &state);

// Internal functions used to run statements and expressions within an action
// body. These are internal functions not used beyond this header and its
// associated source file.

// The scope of this action: maps variable names to their symbolic values.
using ActionContext = std::unordered_map<std::string, z3::expr>;

// Performs a switch case over support statement types and call the
// appropriate function.
pdpi::StatusOr<SymbolicState> RunStatement(const ir::Statement &statement,
                                           const SymbolicState &state,
                                           ActionContext *context);

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
pdpi::StatusOr<SymbolicState> RunAssignmentStatement(
    const ir::AssignmentStatement &assignment, const SymbolicState &state,
    ActionContext *context);

// Constructs a symbolic expression corresponding to this value, according
// to its type.
pdpi::StatusOr<z3::expr> RunRValue(const ir::RValue &rvalue,
                                   const SymbolicState &state,
                                   ActionContext *context);

// Extract the field symbolic value from the symbolic state.
pdpi::StatusOr<z3::expr> RunFieldValue(const ir::FieldValue &field_value,
                                       const SymbolicState &state,
                                       ActionContext *context);

// Looks up the symbolic value of the variable in the action scope.
pdpi::StatusOr<z3::expr> RunVariable(const ir::Variable &variable,
                                     const SymbolicState &state,
                                     ActionContext *context);

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_ACTION_H_
