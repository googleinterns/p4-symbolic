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

// Contains functions used to symbolically evaluate P4 tables and their entries.
// A table is turned into a sequence of if-conditions (one per entry),
// each condition corresponds to having that entry matched on, and the
// corresponding then body invokes the appropriate symbolic action expression
// with the parameters specified in the entry.

#include "p4_symbolic/symbolic/table.h"

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/util.h"

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
    const ir::Table &table, const ir::TableEntry &entry,
    const SymbolicPerPacketState &state) {
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

  // Construct the match condition expression.
  z3::expr condition_expression = Z3_CONTEXT.bool_val(true);
  for (const auto &[id, match] :
       table.table_definition().match_fields_by_id()) {
    p4::config::v1::MatchField match_definition = match.match_field();

    // Match id is unique only within the enclosing table.
    // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
    // Match id starts at 1, and proceeds in the same order the matches are
    // defined in, which is identical to the order they are provided by in
    // the table entries file.
    int value = entry.match_values(id - 1);
    z3::expr value_expr = Z3_CONTEXT.int_val(value);

    // TODO(babman): We should put in the expression of the match from bmv2
    //               json in the IR, and use instead of the name.
    //               @konne mentioned this before in a meeting.
    const std::string &match_string_expression = match_definition.name();
    if (state.metadata.count(match_string_expression) != 1) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrCat("Unknown table match expression ",
                       match_string_expression, " in table ",
                       table.table_definition().preamble().name()));
    }
    ASSIGN_OR_RETURN(
        z3::expr match_expression,
        AnalyzeSingleMatch(match_definition,
                           state.metadata.at(match_string_expression),
                           value_expr));
    condition_expression = condition_expression && match_expression;
  }

  return condition_expression;
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
pdpi::StatusOr<SymbolicPerPacketState> AnalyzeTableEntryAction(
    const ir::Table &table, const ir::TableEntry &entry,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    const SymbolicPerPacketState &state) {
  // Check that the action invoked by entry exists.
  const std::string &table_name = table.table_definition().preamble().name();
  const std::string &action_name = entry.action();
  if (actions.count(action_name) != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table_name, " referring to unknown action ", action_name));
  }

  // Instantiate the action's symbolic expression with the entry values.
  const ir::Action &action = actions.at(action_name);
  return action::EvaluateAction(action, entry.action_parameters(), state);
}

}  // namespace

pdpi::StatusOr<SymbolicPerPacketStateAndMatch> EvaluateTable(
    const ir::Table &table, const std::vector<ir::TableEntry> &entries,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    const SymbolicPerPacketState &state) {
  // The overall structure describing the match on this table.
  SymbolicTableMatch table_match = {
      Z3_CONTEXT.bool_val(false),  // No match yet!
      Z3_CONTEXT.int_val(-1),      // No match index.
      Z3_CONTEXT.int_val(-1)       // Placeholder value.
  };
  // Accumulator state, initially same as input state.
  SymbolicPerPacketState table_state = state;

  // The table semantically is just a bunch of if conditions, one per
  // table entry, we construct this big if-elseif-...-else construct via
  // this simpler representation.
  // Traverse in reverse order: from least to highest priority, since we are
  // building the if-elseif-...-else statement inside out.
  for (int row = entries.size() - 1; row >= 0; row--) {
    const ir::TableEntry &entry = entries.at(row);
    ASSIGN_OR_RETURN(z3::expr row_match,
                     AnalyzeTableEntryCondition(table, entry, state));
    ASSIGN_OR_RETURN(SymbolicPerPacketState row_state,
                     AnalyzeTableEntryAction(table, entry, actions, state));

    // Using this alias makes it simpler to put constraints on packet later.
    table_match.matched = table_match.matched || row_match;
    table_match.entry_index =
        z3::ite(row_match, Z3_CONTEXT.int_val(row), table_match.entry_index);

    // The solver state is changed accordingly if the row was matched.
    table_state =
        util::MergeStatesOnCondition(table_state, row_state, row_match);
  }

  return SymbolicPerPacketStateAndMatch{table_state, table_match};
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
