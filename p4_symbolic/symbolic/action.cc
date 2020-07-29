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
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

gutil::StatusOr<SymbolicHeaders> EvaluateStatement(
    const ir::Statement &statement, const SymbolicHeaders &headers,
    ActionContext *context) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment: {
      return EvaluateAssignmentStatement(statement.assignment(), headers,
                                         context);
    }
    case ir::Statement::kDrop: {
      SymbolicHeaders result = headers;
      result.at("$dropped$") = TypedExpr(Z3Context().bool_val(true));
      return result;
    }
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context->action_name, " contains unsupported statement ",
          statement.DebugString()));
  }
}

// Constructs a symbolic expression for the assignment value, and either
// constrains it in an enclosing assignment expression, or stores it in
// the action scope.
gutil::StatusOr<SymbolicHeaders> EvaluateAssignmentStatement(
    const ir::AssignmentStatement &assignment, const SymbolicHeaders &headers,
    ActionContext *context) {
  // Evaluate RValue recursively, evaluate LValue in this function, then
  // assign RValue to the scope at LValue.
  ASSIGN_OR_RETURN(TypedExpr right,
                   EvaluateRValue(assignment.right(), headers, context));

  switch (assignment.left().lvalue_case()) {
    case ir::LValue::kFieldValue: {
      SymbolicHeaders modified_headers = headers;
      const ir::FieldValue &field_value = assignment.left().field_value();
      std::string field_name = absl::StrFormat(
          "%s.%s", field_value.header_name(), field_value.field_name());
      if (modified_headers.count(field_name) != 1) {
        return absl::UnimplementedError(absl::StrCat(
            "Action ", context->action_name, " refers to unknown header field ",
            field_value.DebugString()));
      }

      modified_headers.at(field_name) = right;
      return modified_headers;
    }

    case ir::LValue::kVariableValue: {
      const std::string &variable = assignment.left().variable_value().name();
      context->scope.insert_or_assign(variable, right);
      return headers;
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context->action_name, " contains unsupported LValue ",
          assignment.left().DebugString()));
  }
}

// Constructs a symbolic expression corresponding to this value, according
// to its type.
gutil::StatusOr<TypedExpr> EvaluateRValue(const ir::RValue &rvalue,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return EvaluateFieldValue(rvalue.field_value(), headers, context);

    case ir::RValue::kHexstrValue:
      return EvaluateHexStr(rvalue.hexstr_value(), headers, context);

    case ir::RValue::kBoolValue:
      return EvaluateBool(rvalue.bool_value(), headers, context);

    case ir::RValue::kStringValue:
      return EvaluateString(rvalue.string_value(), headers, context);

    case ir::RValue::kVariableValue:
      return EvaluateVariable(rvalue.variable_value(), headers, context);

    case ir::RValue::kExpressionValue:
      return EvaluateRExpression(rvalue.expression_value(), headers, context);

    default:
      return absl::UnimplementedError(
          absl::StrCat("Action ", context->action_name,
                       " contains unsupported RValue ", rvalue.DebugString()));
  }
}

// Extract the field symbolic value from the symbolic headers.
gutil::StatusOr<TypedExpr> EvaluateFieldValue(const ir::FieldValue &field_value,
                                              const SymbolicHeaders &headers,
                                              ActionContext *context) {
  std::string field_name = absl::StrFormat("%s.%s", field_value.header_name(),
                                           field_value.field_name());
  if (headers.count(field_name) != 1) {
    return absl::UnimplementedError(absl::StrCat(
        "Action ", context->action_name, " refers to unknown header field ",
        field_value.DebugString()));
  }

  return headers.at(field_name);
}

// Turns bmv2 values to Symbolic Expressions.
gutil::StatusOr<TypedExpr> EvaluateHexStr(const ir::HexstrValue &hexstr,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context) {
  if (hexstr.negative()) {
    return absl::UnimplementedError(
        "Negative hex string values are not supported!");
  }

  ASSIGN_OR_RETURN(pdpi::IrValue parsed_value,
                   util::StringToIrValue(hexstr.value()));
  return util::IrValueToZ3Expr(parsed_value);
}

gutil::StatusOr<TypedExpr> EvaluateBool(const ir::BoolValue &bool_value,
                                        const SymbolicHeaders &headers,
                                        ActionContext *context) {
  return TypedExpr(Z3Context().bool_val(bool_value.value()));
}

gutil::StatusOr<TypedExpr> EvaluateString(const ir::StringValue &string_value,
                                          const SymbolicHeaders &headers,
                                          ActionContext *context) {
  return TypedExpr(Z3Context().string_val(string_value.value().c_str()));
}

// Looks up the symbolic value of the variable in the action scope.
gutil::StatusOr<TypedExpr> EvaluateVariable(const ir::Variable &variable,
                                            const SymbolicHeaders &headers,
                                            ActionContext *context) {
  std::string variable_name = variable.name();
  if (context->scope.count(variable_name) != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Action ", context->action_name,
                     " refers to undefined variable ", variable_name));
  }

  return context->scope.at(variable_name);
}

// Recursively evaluate expressions.
gutil::StatusOr<TypedExpr> EvaluateRExpression(const ir::RExpression &expr,
                                               const SymbolicHeaders &headers,
                                               ActionContext *context) {
  // TODO(babman): support remaining expressions.
  switch (expr.expression_case()) {
    case ir::RExpression::kBinaryExpression: {
      ir::BinaryExpression bin_expr = expr.binary_expression();
      ASSIGN_OR_RETURN(TypedExpr left,
                       EvaluateRValue(bin_expr.left(), headers, context));
      ASSIGN_OR_RETURN(TypedExpr right,
                       EvaluateRValue(bin_expr.right(), headers, context));
      switch (bin_expr.operation()) {
        case ir::BinaryExpression::PLUS:
          return left + right;
        case ir::BinaryExpression::MINUS:
          return left - right;
        case ir::BinaryExpression::TIMES:
          return left * right;
        case ir::BinaryExpression::LEFT_SHIT:
          return TypedExpr::shl(left, right);
        case ir::BinaryExpression::RIGHT_SHIFT:
          return TypedExpr::shr(left, right);
        case ir::BinaryExpression::EQUALS:
          return left == right;
        case ir::BinaryExpression::NOT_EQUALS:
          return !(left == right);
        case ir::BinaryExpression::GREATER:
          return left > right;
        case ir::BinaryExpression::GREATER_EQUALS:
          return left >= right;
        case ir::BinaryExpression::LESS:
          return left < right;
        case ir::BinaryExpression::LESS_EQUALS:
          return left <= right;
        case ir::BinaryExpression::AND:
          return left && right;
        case ir::BinaryExpression::OR:
          return left || right;
        case ir::BinaryExpression::BIT_AND:
          return left & right;
        case ir::BinaryExpression::BIT_OR:
          return left | right;
        case ir::BinaryExpression::BIT_XOR:
          return left ^ right;
        default:
          return absl::UnimplementedError(
              absl::StrCat("Action ", context->action_name,
                           " contains unsupported BinaryExpression ",
                           bin_expr.DebugString()));
      }
      break;
    }

    case ir::RExpression::kUnaryExpression: {
      ir::UnaryExpression un_expr = expr.unary_expression();
      ASSIGN_OR_RETURN(TypedExpr operand,
                       EvaluateRValue(un_expr.operand(), headers, context));
      switch (un_expr.operation()) {
        case ir::UnaryExpression::NOT:
          return !operand;
        case ir::UnaryExpression::BIT_NEGATION:
          return ~operand;
        default:
          return absl::UnimplementedError(absl::StrCat(
              "Action ", context->action_name,
              " contains unsupported UnaryExpression ", un_expr.DebugString()));
      }
      break;
    }

    case ir::RExpression::kTernaryExpression: {
      ir::TernaryExpression tern_expr = expr.ternary_expression();
      ASSIGN_OR_RETURN(TypedExpr condition,
                       EvaluateRValue(tern_expr.condition(), headers, context));
      ASSIGN_OR_RETURN(TypedExpr left,
                       EvaluateRValue(tern_expr.left(), headers, context));
      ASSIGN_OR_RETURN(TypedExpr right,
                       EvaluateRValue(tern_expr.right(), headers, context));
      return TypedExpr::ite(condition, left, right);
    }

    case ir::RExpression::kBuiltinExpression:
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Action ", context->action_name, " contains unsupported RExpression ",
          expr.DebugString()));
  }
}

// Symbolically evaluates the given action on the given symbolic parameters.
// This produces a symbolic expression on the symbolic parameters that is
// semantically equivalent to the behavior of the action on its concrete
// parameters.
gutil::StatusOr<SymbolicHeaders> EvaluateAction(
    const ir::Action &action,
    const google::protobuf::RepeatedPtrField<
        pdpi::IrActionInvocation::IrActionParam> &args,
    const SymbolicHeaders &headers) {
  // Construct this action's context.
  ActionContext context;
  context.action_name = action.action_definition().preamble().name();

  // Add action parameters to scope.
  const auto &parameters = action.action_definition().params_by_id();
  if (static_cast<int>(parameters.size()) != args.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Action ", action.action_definition().preamble().name(),
                     " called with incompatible number of parameters"));
  }

  // Find each parameter value in argument by parameter's name.
  for (size_t i = 1; i <= parameters.size(); i++) {
    // parameter id is the same as its index + 1.
    const pdpi::IrActionDefinition::IrActionParamDefinition &parameter =
        parameters.at(i);
    const std::string &parameter_name = parameter.param().name();
    ASSIGN_OR_RETURN(TypedExpr parameter_value,
                     util::IrValueToZ3Expr(args.at(i - 1).value()));
    context.scope.insert({parameter_name, parameter_value});
  }

  // Iterate over the body in order, and evaluate each statement.
  SymbolicHeaders result = headers;
  for (const auto &statement : action.action_implementation().action_body()) {
    ASSIGN_OR_RETURN(result, EvaluateStatement(statement, result, &context));
  }

  return result;
}

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic
