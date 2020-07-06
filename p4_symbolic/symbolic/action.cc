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

#include "p4_symbolic/symbolic/action.h"

#include <vector>

#include "absl/status/status.h"
#include "p4_symbolic/symbolic/names.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

namespace {

// Assigns the field a symbolic variable (alias).
pdpi::StatusOr<z3::expr> AnalyzeFieldValue(const ir::FieldValue &field_value,
                                           const SolverState &solver_state,
                                           ActionContext *context) {
  std::string field_variable_name = names::ForHeaderField(field_value);
  return solver_state.context->int_const(field_variable_name.c_str());
}

// Looks up the symbolic value of the variable in the action scope.
pdpi::StatusOr<z3::expr> AnalyzeVariable(const ir::Variable &variable,
                                         const SolverState &solver_state,
                                         ActionContext *context) {
  const std::string &variable_name = variable.name();
  if (context->scope.count(variable_name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Action ", context->action_name,
                     " uses undefined variable ", variable_name));
  }
  return context->scope.at(variable_name);
}

// Constructs a symbolic expression corresponding to this value, according
// to its type.
pdpi::StatusOr<z3::expr> AnalyzeRValue(const ir::RValue &rvalue,
                                       const SolverState &solver_state,
                                       ActionContext *context) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return AnalyzeFieldValue(rvalue.field_value(), solver_state, context);

    case ir::RValue::kVariableValue:
      return AnalyzeVariable(rvalue.variable_value(), solver_state, context);

    default:
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrCat("Action ", context->action_name,
                       " contains unsupported RValue ", rvalue.DebugString()));
  }
}

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
pdpi::StatusOr<z3::expr> AnalyzeAssignmentStatement(
    const ir::AssignmentStatement &assignment, const SolverState &solver_state,
    ActionContext *context) {
  ASSIGN_OR_RETURN(z3::expr right,
                   AnalyzeRValue(assignment.right(), solver_state, context));

  switch (assignment.left().lvalue_case()) {
    case ir::LValue::kFieldValue: {
      ASSIGN_OR_RETURN(z3::expr field_expr,
                       AnalyzeFieldValue(assignment.left().field_value(),
                                         solver_state, context));

      // TODO(babman): this will fail if action modifies the same field
      //               several times.
      return field_expr == right;
    }

    case ir::LValue::kVariableValue: {
      const std::string &variable = assignment.left().variable_value().name();
      if (context->scope.count(variable) == 0) {
        context->scope.insert({variable, right});
      } else {
        context->scope.at(variable) = right;
      }
      return solver_state.context->bool_val(true);
    }

    default:
      return absl::Status(absl::StatusCode::kUnimplemented,
                          absl::StrCat("Action ", context->action_name,
                                       " contains unsupported LValue ",
                                       assignment.left().DebugString()));
  }
}

// Performs a switch case over support statement types and call the
// appropriate function.
pdpi::StatusOr<z3::expr> AnalyzeStatement(const ir::Statement &statement,
                                          const SolverState &solver_state,
                                          ActionContext *context) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment:
      return AnalyzeAssignmentStatement(statement.assignment(), solver_state,
                                        context);

    default:
      return absl::Status(absl::StatusCode::kUnimplemented,
                          absl::StrCat("Action ", context->action_name,
                                       " contains unsupported statement ",
                                       statement.DebugString()));
  }
}

}  // namespace

pdpi::StatusOr<ActionSymbolicTrace> AnalyzeAction(
    const ir::Action &action, const SolverState &solver_state) {
  const std::string &action_name = action.action_definition().preamble().name();

  // Construct this action's context.
  ActionContext context;
  context.action_name = action_name;

  // Add action parameters to scope.
  std::vector<z3::expr> parameters_vector;
  const auto &parameters = action.action_definition().params_by_id();
  for (size_t i = 1; i <= parameters.size(); i++) {  // In order of definition.
    const pdpi::ir::IrActionDefinition::IrActionParamDefinition &parameter =
        parameters.at(i);
    const std::string &parameter_name = parameter.param().name();
    std::string variable_name = names::ForActionParameter(action, parameter);
    z3::expr variable = solver_state.context->int_const(variable_name.c_str());
    context.scope.insert({parameter_name, variable});
    parameters_vector.push_back(variable);
  }

  // Iterate over the body in order, and analyze each statement.
  z3::expr body = solver_state.context->bool_val(true);
  for (const auto &statement : action.action_implementation().action_body()) {
    ASSIGN_OR_RETURN(z3::expr e,
                     AnalyzeStatement(statement, solver_state, &context));
    body = body && e;
  }

  return ActionSymbolicTrace(action_name, parameters_vector, body);
}

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic
