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

// TODO(babman): sort entries (and thus order if statements) by priority.

#include "p4_symbolic/symbolic/table.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "p4_symbolic/symbolic/names.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

// Analyze a single match that is part of a table entry.
// Constructs a symbolic expression that semantically corresponds to this
// match.
pdpi::StatusOr<z3::expr> AnalyzeSingleMatch(
    p4::config::v1::MatchField match_definition,
    const z3::expr &field_expression, const z3::expr &match_value) {
  if (match_definition.match_case() != p4::config::v1::MatchField::kMatchType) {
    // Arch-specific match type.
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrCat("Found match with non-standard type"));
  }

  // TODO(babman): Support the other match types.
  switch (match_definition.match_type()) {
    case p4::config::v1::MatchField::EXACT:
      return field_expression == match_value;

    default:
      return absl::Status(absl::StatusCode::kInvalidArgument,
                          absl::StrCat("Found unsupported match type ",
                                       match_definition.match_type()));
  }
}

// Constructs a symbolic expression that is true if and only if this entry
// is matched on.
pdpi::StatusOr<z3::expr> AnalyzeTableEntryCondition(
    const ir::TableEntry &entry, const SolverState &solver_state,
    const ir::Table &table) {
  // Make sure number of match keys is the same in the table definition and
  // table entry.
  if (table.table_definition().match_fields_by_id_size() !=
      entry.match_values_size()) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table.table_definition().preamble().name(),
                     " with wrong match fields count"));
  }

  // Construct the expressions.
  z3::expr condition_expression = solver_state.context->bool_val(true);
  for (const auto &[id, match] :
       table.table_definition().match_fields_by_id()) {
    p4::config::v1::MatchField match_definition = match.match_field();

    // Match id is unique only within the enclosing table.
    // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
    // Match id starts at 1, and proceeds in the same order the matches are
    // defined in, which is identical to the order they are provided by in
    // the table entries file.
    int value = entry.match_values(id - 1);

    // TODO(babman): We should put in the expression of the match from bmv2
    //               json in the IR, and use instead of the name.
    //               @konne mentioned this before in a meeting.
    const std::string &match_string_expression = match_definition.name();
    ASSIGN_OR_RETURN(z3::expr match_expression,
                     AnalyzeSingleMatch(match_definition,
                                        solver_state.context->int_const(
                                            match_string_expression.c_str()),
                                        solver_state.context->int_val(value)));
    condition_expression = condition_expression && match_expression;
  }

  return condition_expression;
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
pdpi::StatusOr<z3::expr> AnalyzeTableEntryAction(
    const ir::TableEntry &entry, const SolverState &solver_state,
    const ir::Table &table) {
  // Check that the action invoked by entry exists.
  const std::string &table_name = table.table_definition().preamble().name();
  const std::string &action_name = entry.action();
  if (solver_state.action_map.count(action_name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table_name, " referring to unknown action ", action_name));
  }

  // Instantiate the action's symbolic expression with the entry values.
  return solver_state.action_map.at(action_name)
      .instantiate(entry.action_parameters());
}

}  // namespace

pdpi::StatusOr<z3::expr> AnalyzeTable(const ir::Table &table,
                                      const SolverState &solver_state) {
  const std::string &table_name = table.table_definition().preamble().name();

  // The table semantically is just a bunch of if conditions, one per
  // table entry, we construct this big if-elseif-...-else construct via
  // this simpler representation.
  // <condition to satisfy, action to invoke when condition is satisfied>
  std::vector<std::pair<z3::expr, z3::expr>> conditions;
  z3::expr table_aliases = solver_state.context->bool_val(true);

  for (int row = 0; row < table.table_implementation().entries_size(); row++) {
    const ir::TableEntry &entry = table.table_implementation().entries(row);
    ASSIGN_OR_RETURN(z3::expr match_expression,
                     AnalyzeTableEntryCondition(entry, solver_state, table));
    ASSIGN_OR_RETURN(z3::expr action_expression,
                     AnalyzeTableEntryAction(entry, solver_state, table));

    // Using this alias makes it simpler to put constraints on packet later.
    z3::expr entry_alias = solver_state.context->bool_const(
        names::ForTableEntry(table_name, row).c_str());
    table_aliases = table_aliases && (entry_alias == match_expression);
    conditions.push_back(
        std::make_pair(std::move(entry_alias), std::move(action_expression)));
  }

  // Start from the else case, and "onion" else-if cases around  it.
  z3::expr if_elseif_else =
      solver_state.context->bool_const(names::ForDroppedPacket().c_str());
  for (int i = conditions.size() - 1; i >= 0; i--) {
    const auto &[condition, body] = conditions.at(i);
    if_elseif_else = z3::ite(condition, body, if_elseif_else);
  }
  return table_aliases && if_elseif_else;
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
