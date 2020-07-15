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

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

gutil::StatusOr<SymbolicPerPacketState> EvaluateStatement(
    const ir::Statement &statement, const SymbolicPerPacketState &state,
    ActionContext *context) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment:
      return EvaluateAssignmentStatement(statement.assignment(), state,
                                         context);

    default:
      return absl::Status(absl::StatusCode::kUnimplemented,
                          absl::StrCat("Action ", context->action_name,
                                       " contains unsupported statement ",
                                       statement.DebugString()));
  }
}

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
gutil::StatusOr<SymbolicPerPacketState> EvaluateAssignmentStatement(
    const ir::AssignmentStatement &assignment,
    const SymbolicPerPacketState &state, ActionContext *context) {
  // Evaluate RValue recursively, evaluate LValue in this function, then
  // assign RValue to the scope at LValue.
  ASSIGN_OR_RETURN(z3::expr right,
                   EvaluateRValue(assignment.right(), state, context));

  switch (assignment.left().lvalue_case()) {
    case ir::LValue::kFieldValue: {
      const ir::FieldValue &field_value = assignment.left().field_value();
      // TODO(babman): Better handling of metadata and headers in general.
      //               What should be hardcoded? probably only the headers
      //               used for packet generation.
      //               Need a better way to translate between hardcoded names
      //               and strings / FieldValue objects.
      //               Need to detect fields automatically. We already have this
      //               information in bmv2, and we already did it in a previous
      //               version of this code.
      SymbolicPerPacketState modified_state = state;
      std::string field_name = absl::StrFormat(
          "%s.%s", field_value.header_name(), field_value.field_name());
      if (modified_state.metadata.count(field_name) != 1) {
        return absl::Status(absl::StatusCode::kUnimplemented,
                            absl::StrCat("Action ", context->action_name,
                                         " refers to unknown header field ",
                                         field_value.DebugString()));
      }

      modified_state.metadata.at(field_name) = right;
      return modified_state;
    }

    case ir::LValue::kVariableValue: {
      const std::string &variable = assignment.left().variable_value().name();
      context->scope.insert_or_assign(variable, right);
      return state;
    }

    default:
      return absl::Status(absl::StatusCode::kUnimplemented,
                          absl::StrCat("Action ", context->action_name,
                                       " contains unsupported LValue ",
                                       assignment.left().DebugString()));
  }
}

// Constructs a symbolic expression corresponding to this value, according
// to its type.
gutil::StatusOr<z3::expr> EvaluateRValue(const ir::RValue &rvalue,
                                         const SymbolicPerPacketState &state,
                                         ActionContext *context) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return EvaluateFieldValue(rvalue.field_value(), state, context);

    case ir::RValue::kVariableValue:
      return EvaluateVariable(rvalue.variable_value(), state, context);

    default:
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrCat("Action ", context->action_name,
                       " contains unsupported RValue ", rvalue.DebugString()));
  }
}

// Extract the field symbolic value from the symbolic state.
gutil::StatusOr<z3::expr> EvaluateFieldValue(
    const ir::FieldValue &field_value, const SymbolicPerPacketState &state,
    ActionContext *context) {
  std::string field_name = absl::StrFormat("%s.%s", field_value.header_name(),
                                           field_value.field_name());
  if (state.metadata.count(field_name) != 1) {
    return absl::Status(absl::StatusCode::kUnimplemented,
                        absl::StrCat("Action ", context->action_name,
                                     " refers to unknown header field ",
                                     field_value.DebugString()));
  }

  return state.metadata.at(field_name);
}

// Looks up the symbolic value of the variable in the action scope.
gutil::StatusOr<z3::expr> EvaluateVariable(const ir::Variable &variable,
                                           const SymbolicPerPacketState &state,
                                           ActionContext *context) {
  std::string variable_name = variable.name();
  if (context->scope.count(variable_name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Action ", context->action_name,
                     " refers to undefined variable ", variable_name));
  }

  return context->scope.at(variable_name);
}

// Symbolically evaluates the given action on the given symbolic parameters.
// This produces a symbolic expression on the symbolic parameters that is
// semantically equivalent to the behavior of the action on its concrete
// parameters.
gutil::StatusOr<SymbolicPerPacketState> EvaluateAction(
    const ir::Action &action, const google::protobuf::RepeatedField<int> &args,
    const SymbolicPerPacketState &state) {
  // Construct this action's context.
  ActionContext context;
  context.action_name = action.action_definition().preamble().name();

  // Add action parameters to scope.
  const auto &parameters = action.action_definition().params_by_id();
  if (static_cast<int>(parameters.size()) != args.size()) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Action ", action.action_definition().preamble().name(),
                     " called with incompatible number of parameters"));
  }

  for (size_t i = 1; i <= parameters.size(); i++) {  // In order of definition.
    const pdpi::IrActionDefinition::IrActionParamDefinition &parameter =
        parameters.at(i);
    const std::string &parameter_name = parameter.param().name();
    z3::expr parameter_value = Z3Context().int_val(args.at(i - 1));
    context.scope.insert({parameter_name, parameter_value});
  }

  // Iterate over the body in order, and evaluate each statement.
  SymbolicPerPacketState result = state;
  for (const auto &statement : action.action_implementation().action_body()) {
    ASSIGN_OR_RETURN(result, EvaluateStatement(statement, result, &context));
  }

  return result;
}

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic
