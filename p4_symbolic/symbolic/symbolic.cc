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

#include "p4_symbolic/symbolic/symbolic.h"

#include <iostream>

#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"

namespace p4_symbolic {
namespace symbolic {

absl::Status Analyzer::Analyze(ir::P4Program program) {
  this->program_ = program;

  for (const auto &[_, header_type] : program.headers()) {
    RETURN_IF_ERROR(this->AnalyzeHeaderType(header_type));
  }

  // Visit actions first to define symbolic expressions for their parameters.
  // Then visit tables, since their entries will use the action parameters
  // symbolic expressions.
  // TODO(babman): ensure this order is fine for more complex workflows,
  //               e.g. VRF, we may need to traverse actions + tables in order,
  //               starting from init_table?
  for (const auto &[_, action] : program.actions()) {
    RETURN_IF_ERROR(this->AnalyzeAction(action));
  }
  for (const auto &[_, table] : program.tables()) {
    RETURN_IF_ERROR(this->AnalyzeTable(table));
  }

  return absl::OkStatus();
}

absl::Status Analyzer::AnalyzeHeaderType(const ir::HeaderType &header_type) {
  const std::string &header_type_name = header_type.name();
  for (const auto &[_, header_field] : header_type.fields()) {
    RETURN_IF_ERROR(this->AnalyzeHeaderField(header_field, header_type_name));
  }
  return absl::OkStatus();
}

absl::Status Analyzer::AnalyzeHeaderField(const ir::HeaderField &header_field,
                                          const std::string &header_type) {
  const std::string &full_name =
      absl::StrFormat("%s.%s", header_type, header_field.name());
  this->fields_map_.insert(
      {full_name, this->context_.int_const(full_name.c_str())});
  return absl::OkStatus();
}

absl::Status Analyzer::AnalyzeTable(const ir::Table &table) {
  const std::string &table_name = table.table_definition().preamble().name();

  // TODO(babman): This assumes any action can only be used by a single table.
  std::unordered_map<std::string, z3::expr> actions_to_match_exprs;

  for (int row = 0; row < table.table_implementation().entries_size(); row++) {
    const ir::TableEntry &entry = table.table_implementation().entries(row);
    const std::string &complete_match_name =
        absl::StrFormat("%s_%d", table_name, row);

    // Symbolic variable representing this row being matched.
    z3::expr match_variable =
        this->context_.bool_const(complete_match_name.c_str());
    this->entries_map_.insert({complete_match_name, match_variable});

    // Iterate over all fields constituting a complete match.
    // A symbolic expressions is created for every partial match over a field.
    std::vector<z3::expr> partial_matches;
    for (const auto &[id, match] :
         table.table_definition().match_fields_by_id()) {
      p4::config::v1::MatchField match_definition = match.match_field();
      const std::string &match_name =
          absl::StrFormat("%s_%d", complete_match_name, id);

      // Match id is unique only within the enclosing table.
      // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
      // Match id starts at 1, and proceeds in the same order the matches are
      // defined in, which is identical to the order they are provided by in
      // the table entries file.
      int index = id - 1;  // index of corresponding value in the table entry.

      // TODO(babman): Support bit vectors.
      int value = entry.match_values(index);

      // TODO(babman): We should put in the expression of the match from bmv2
      //               json in the IR, and use instead of the name.
      //               @konne mentioned this before in a meeting.
      const std::string &header_field_symbolic_name = match_definition.name();
      if (this->fields_map_.count(header_field_symbolic_name) != 1) {
        return absl::Status(absl::StatusCode::kInvalidArgument,
                            absl::StrCat("Table ", table_name,
                                         " has match on unknown expression ",
                                         header_field_symbolic_name));
      }
      const z3::expr &header_field_expr =
          this->fields_map_.at(header_field_symbolic_name);

      // Return an error if the match type is unsupported.
      if (match_definition.match_case() !=
          p4::config::v1::MatchField::kMatchType) {
        // Arch-specific match type.
        return absl::Status(absl::StatusCode::kInvalidArgument,
                            absl::StrCat("Table ", table_name,
                                         " has match with non-standard type"));
      }

      // Create symbolic match expression using the value from entry,
      // and the symbolic expression of the matched field/expression.
      switch (match_definition.match_type()) {
        case p4::config::v1::MatchField::EXACT:
          partial_matches.push_back(header_field_expr == value);
          break;

        default:  // TODO(babman): support the other match types.
          return absl::Status(
              absl::StatusCode::kInvalidArgument,
              absl::StrCat("Table ", table_name, " has unsupported match type ",
                           match_definition.match_type()));
      }
    }

    // Define an expression expressing what it means to match this row.
    // This complete match is the conjunction of all above partial matches.
    // TODO(babman): Add support for priorities, by adding negation of all
    //               higher priority matches to the conjunction.
    //               A better way to do this first, is sort by priority,
    //               and keep a running vector of all previously created
    //               complete symbolic match expressions, and negate those.
    z3::expr complete_match_expr = partial_matches[0];
    for (size_t i = 1; i < partial_matches.size(); i++) {
      complete_match_expr = complete_match_expr && partial_matches[i];
    }
    this->constraints_.push_back(match_variable == complete_match_expr);

    // Constrain the values of the action parameter when this entry is matched.
    const std::string &action_name = entry.action();
    if (this->program_.actions().count(action_name) != 1) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrCat("Table ", table_name, " has match entry ",
                       entry.DebugString(), " referring to unknown action ",
                       action_name));
    }

    const ir::Action &action = this->program_.actions().at(action_name);
    const auto &parameters = action.action_definition().params_by_id();
    for (int p = 0; p < entry.action_parameters_size(); p++) {
      // TODO(babman): switch to bit vectors.
      int value = entry.action_parameters(p);
      if (parameters.count(p + 1) != 1) {
        return absl::Status(
            absl::StatusCode::kInvalidArgument,
            absl::StrCat("Table ", table_name, " has match entry ",
                         entry.DebugString(), " was too many parameters"));
      }
      const std::string &parameter_name = parameters.at(p + 1).param().name();
      const std::string &full_parameter_name =
          absl::StrFormat("%s.%s", action_name, parameter_name);
      if (this->variables_map_.count(full_parameter_name) != 1) {
        return absl::Status(
            absl::StatusCode::kInvalidArgument,
            absl::StrCat(
                "Table ", table_name, " has match entry ", entry.DebugString(),
                " referring to un-analyzed parameter ", full_parameter_name));
      }

      this->constraints_.push_back(
          z3::implies(match_variable,
                      this->variables_map_.at(full_parameter_name) == value));
    }

    // Mark that the action will be invoked by this match entry.
    z3::expr action_expr = match_variable;
    if (actions_to_match_exprs.count(action_name) != 0) {
      action_expr = actions_to_match_exprs.at(action_name) || match_variable;
    }
    actions_to_match_exprs.insert_or_assign(action_name, action_expr);
  }

  // An action is invoked when one of the matches refering to it are met.
  for (const auto &[action_name, action_expr] : actions_to_match_exprs) {
    if (this->actions_map_.count(action_name) != 1) {
      return absl::Status(absl::StatusCode::kInvalidArgument,
                          absl::StrCat("Table ", table_name,
                                       " has match entry(s) referring to "
                                       " un-analyzed action ",
                                       action_name));
    }
    this->constraints_.push_back(this->actions_map_.at(action_name) ==
                                 action_expr);
  }

  return absl::OkStatus();
}

absl::Status Analyzer::AnalyzeAction(const ir::Action &action) {
  const std::string &action_name = action.action_definition().preamble().name();

  // Create a symbolic variable corresponding to this action being called.
  z3::expr action_variable = this->context_.bool_const(action_name.c_str());
  this->actions_map_.insert({action_name, action_variable});

  // Create a symbolic variable corresponding to every variable.
  for (const auto &[name, _] : action.action_implementation().variables()) {
    const std::string &full_variable_name =
        absl::StrFormat("%s.%s", action_name, name);
    // TODO(babman): Take type into consideration when using bit vectors.
    this->variables_map_.insert(
        {full_variable_name,
         this->context_.int_const(full_variable_name.c_str())});
  }

  // Analyze every statement in the body one at a time.
  for (const auto &statement : action.action_implementation().action_body()) {
    RETURN_IF_ERROR(
        this->AnalyzeStatement(statement, action_variable, action_name));
  }

  return absl::OkStatus();
}

absl::Status Analyzer::AnalyzeStatement(const ir::Statement &statement,
                                        const z3::expr &precondition,
                                        const std::string &action) {
  switch (statement.statement_case()) {
    case ir::Statement::kAssignment:
      return this->AnalyzeAssignmentStatement(statement.assignment(),
                                              precondition, action);

    default:
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrCat("Action ", action, " contains unsupported statement ",
                       statement.DebugString()));
  }
}

absl::Status Analyzer::AnalyzeAssignmentStatement(
    const ir::AssignmentStatement &assignment, const z3::expr &precondition,
    const std::string &action) {
  ASSIGN_OR_RETURN(z3::expr * left, this->AnalyzeLValue(assignment.left(),
                                                        precondition, action));
  ASSIGN_OR_RETURN(z3::expr * right, this->AnalyzeRValue(assignment.right(),
                                                         precondition, action));
  this->constraints_.push_back(z3::implies(precondition, (*left == *right)));
  return absl::OkStatus();
}

pdpi::StatusOr<z3::expr *> Analyzer::AnalyzeLValue(const ir::LValue &lvalue,
                                                   const z3::expr &precondition,
                                                   const std::string &action) {
  switch (lvalue.lvalue_case()) {
    case ir::LValue::kFieldValue:
      return this->AnalyzeFieldValue(lvalue.field_value(), precondition,
                                     action);

    case ir::LValue::kVariableValue:
      return this->AnalyzeVariable(lvalue.variable_value(), precondition,
                                   action);

    default:
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrCat("Action ", action, " contains unsupported LValue ",
                       lvalue.DebugString()));
  }
}

pdpi::StatusOr<z3::expr *> Analyzer::AnalyzeRValue(const ir::RValue &rvalue,
                                                   const z3::expr &precondition,
                                                   const std::string &action) {
  switch (rvalue.rvalue_case()) {
    case ir::RValue::kFieldValue:
      return this->AnalyzeFieldValue(rvalue.field_value(), precondition,
                                     action);

    case ir::RValue::kVariableValue:
      return this->AnalyzeVariable(rvalue.variable_value(), precondition,
                                   action);

    default:
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrCat("Action ", action, " contains unsupported RValue ",
                       rvalue.DebugString()));
  }
}

pdpi::StatusOr<z3::expr *> Analyzer::AnalyzeFieldValue(
    const ir::FieldValue &field_value, const z3::expr &precondition,
    const std::string &action) {
  const std::string &name = absl::StrFormat("%s.%s", field_value.header_name(),
                                            field_value.field_name());
  if (this->fields_map_.count(name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Action ", action, " referes to unknown field ", name));
  }

  return &this->fields_map_.at(name);
}

pdpi::StatusOr<z3::expr *> Analyzer::AnalyzeVariable(
    const ir::Variable &variable, const z3::expr &precondition,
    const std::string &action) {
  const std::string &name = absl::StrFormat("%s.%s", action, variable.name());
  if (this->variables_map_.count(name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Action ", action, " referes to unknown variable ", name));
  }

  return &this->variables_map_.at(name);
}

std::string Analyzer::DebugSMT() {
  z3::solver solver(this->context_);
  for (const z3::expr &constraint : this->constraints_) {
    solver.add(constraint);
  }
  return solver.to_smt2();
}

pdpi::StatusOr<Packet> Analyzer::FindPacketHittingRow(const std::string &table,
                                                      int row) {
  z3::solver solver(this->context_);
  for (const z3::expr &constraint : this->constraints_) {
    solver.add(constraint);
  }

  const std::string &full_name = absl::StrFormat("%s_%d", table, row);
  if (this->entries_map_.count(full_name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Table %s or row %d do not exist", table, row));
  }
  solver.add(this->entries_map_.at(full_name));

  switch (solver.check()) {
    case z3::unsat:
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Table %s and row %d is impossible to hit", table,
                          row));

    case z3::unknown:
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Could not find packet to hit Table %s and row %d",
                          table, row));

    case z3::sat:
    default:
      z3::model packet_model = solver.get_model();
      std::map<std::string, std::string> output;
      for (const auto &[name, field] : this->fields_map_) {
        if (!field.is_const()) {
          continue;
        }

        z3::func_decl field_decl = field.decl();
        if (packet_model.has_interp(field_decl)) {
          output[name] = packet_model.get_const_interp(field_decl).to_string();
        }
      }

      return output;
  }
}

}  // namespace symbolic
}  // namespace p4_symbolic
