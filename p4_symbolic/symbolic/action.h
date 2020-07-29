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

// Contains functions used to symbolically evaluate actions and their bodies.
// An action is represented as a boolean symbolic z3 expression over
// unconstrained symbolic parameters corresponding to its actual P4 parameters.

#ifndef P4_SYMBOLIC_SYMBOLIC_ACTION_H_
#define P4_SYMBOLIC_SYMBOLIC_ACTION_H_

#include <string>
#include <unordered_map>
#include <vector>

#include "google/protobuf/repeated_field.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/typed.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

// Symbolically evaluates the given action on the given symbolic parameters.
// This produces a symbolic expression on the symbolic parameters that is
// semantically equivalent to the behavior of the action on its concrete
// parameters.
gutil::StatusOr<SymbolicHeaders> EvaluateAction(
    const ir::Action &action,
    const google::protobuf::RepeatedPtrField<
        pdpi::IrActionInvocation::IrActionParam> &args,
    const SymbolicHeaders &headers);

// Internal functions used to Evaluate statements and expressions within an
// action body. These are internal functions not used beyond this header and its
// associated source file.

// The scope of this action: maps local variable names to their symbolic values.
struct ActionContext {
  std::string action_name;
  std::unordered_map<std::string, TypedExpr> scope;
};

// Performs a switch case over support statement types and call the
// appropriate function.
gutil::StatusOr<SymbolicHeaders> EvaluateStatement(
    const ir::Statement &statement, const SymbolicHeaders &headers,
    ActionContext *context);

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
gutil::StatusOr<SymbolicHeaders> EvaluateAssignmentStatement(
    const ir::AssignmentStatement &assignment, const SymbolicHeaders &headers,
    ActionContext *context);

// Constructs a symbolic expression corresponding to this value, according
// to its type.
gutil::StatusOr<TypedExpr> EvaluateRValue(const ir::RValue &rvalue,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context);

// Extract the field symbolic value from the symbolic state.
gutil::StatusOr<TypedExpr> EvaluateFieldValue(const ir::FieldValue &field_value,
                                              const SymbolicHeaders &headers,
                                              ActionContext *context);

// Parse and format literal values as symbolic expression.
gutil::StatusOr<TypedExpr> EvaluateHexStr(const ir::HexstrValue &hexstr,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context);

gutil::StatusOr<TypedExpr> EvaluateBool(const ir::BoolValue &bool_value,
                                        const SymbolicHeaders &headers,
                                        ActionContext *context);

gutil::StatusOr<TypedExpr> EvaluateString(const ir::StringValue &string_value,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context);

// Looks up the symbolic value of the variable in the action scope.
gutil::StatusOr<TypedExpr> EvaluateVariable(const ir::Variable &variable,
                                            const SymbolicHeaders &headers,
                                            ActionContext *context);

// Evaluate expression by recursively evaluating operands and applying the
// symbolic version of the operator to them.
gutil::StatusOr<TypedExpr> EvaluateRExpression(const ir::RExpression &expr,
                                               const SymbolicHeaders &headers,
                                               ActionContext *context);

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_ACTION_H_
