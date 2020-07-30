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
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

// Analyze a single match that is part of a table entry.
// Constructs a symbolic expression that semantically corresponds to this
// match.
gutil::StatusOr<z3::expr> AnalyzeSingleMatch(
    p4::config::v1::MatchField match_definition,
    const z3::expr &field_expression, const pdpi::IrMatch &match) {
  if (match_definition.match_case() != p4::config::v1::MatchField::kMatchType) {
    // Arch-specific match type.
    return absl::InvalidArgumentError(
        absl::StrCat("Found match with non-standard type"));
  }

  // TODO(babman): Support the other match types.
  switch (match_definition.match_type()) {
    case p4::config::v1::MatchField::EXACT: {
      if (match.match_value_case() != pdpi::IrMatch::kExact) {
        return absl::InvalidArgumentError(
            absl::StrCat("Match definition in table has type \"Exact\" but its "
                         "invocation in TableEntry has a different type ",
                         match_definition.DebugString()));
      }
      ASSIGN_OR_RETURN(z3::expr value_expression,
                       util::IrValueToZ3Expr(match.exact()));
      return operators::Eq(field_expression, value_expression);
    }

    case p4::config::v1::MatchField::LPM: {
      if (match.match_value_case() != pdpi::IrMatch::kLpm) {
        return absl::InvalidArgumentError(
            absl::StrCat("Match definition in table has type \"LPM\" but its "
                         "invocation in TableEntry has a different type ",
                         match_definition.DebugString()));
      }

      ASSIGN_OR_RETURN(z3::expr value_expression,
                       util::IrValueToZ3Expr(match.lpm().value()));
      return operators::PrefixEq(
          field_expression, value_expression,
          static_cast<unsigned int>(match.lpm().prefix_length()));
    }

    default:
      return absl::UnimplementedError(absl::StrCat(
          "Found unsupported match type ", match_definition.DebugString()));
  }
}

// Constructs a symbolic expression that is true if and only if this entry
// is matched on.
gutil::StatusOr<z3::expr> AnalyzeTableEntryCondition(
    const ir::Table &table, const pdpi::IrTableEntry &entry,
    const SymbolicHeaders &headers) {
  // Make sure number of match keys is the same in the table definition and
  // table entry.
  const std::string &table_name = table.table_definition().preamble().name();
  if (table.table_definition().match_fields_by_id_size() !=
      entry.matches_size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table_name, " with wrong match fields count"));
  }

  // Construct the match condition expression.
  z3::expr condition_expression = Z3Context().bool_val(true);
  const google::protobuf::Map<std::string, ir::FieldValue> &match_to_fields =
      table.table_implementation().match_name_to_field();
  for (const auto &[id, match_fields] :
       table.table_definition().match_fields_by_id()) {
    p4::config::v1::MatchField match_definition = match_fields.match_field();

    // Match id is unique only within the enclosing table.
    // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
    // Match id starts at 1, and proceeds in the same order the matches are
    // defined in, which is identical to the order they are provided by in
    // the table entries file.
    const pdpi::IrMatch &match = entry.matches(id - 1);

    // We get the match name for pdpi/p4info for simplicity, however that
    // file only contains the match name as a string, which is the same as the
    // match target expression in most cases but not always.
    // For conciseness, we get the corresponding accurate match target from
    // bmv2 by looking up the match name there.
    // In certain cases this is important, e.g. a match defined over field
    // "dstAddr" may have aliases of that field as a match name, but will always
    // have the fully qualified name of the field in the bmv2 format.
    if (match_to_fields.count(match_definition.name()) != 1) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Match key with name \"", match_definition.name(),
          "\" was not found in implementation of table \"", table_name, "\""));
    }

    ir::FieldValue match_field = match_to_fields.at(match_definition.name());
    action::ActionContext fake_context = {table_name, {}};
    ASSIGN_OR_RETURN(
        z3::expr match_field_expr,
        action::EvaluateFieldValue(match_field, headers, &fake_context));
    ASSIGN_OR_RETURN(
        z3::expr match_expression,
        AnalyzeSingleMatch(match_definition, match_field_expr, match));
    ASSIGN_OR_RETURN(condition_expression,
                     operators::And(condition_expression, match_expression));
  }

  return condition_expression;
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
absl::Status AnalyzeTableEntryAction(
    const ir::Table &table, const pdpi::IrTableEntry &entry,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    SymbolicHeaders *headers, const z3::expr &guard) {
  // Check that the action invoked by entry exists.
  const std::string &table_name = table.table_definition().preamble().name();
  const std::string &action_name = entry.action().name();
  if (actions.count(action_name) != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table_name, " referring to unknown action ", action_name));
  }

  // Instantiate the action's symbolic expression with the entry values.
  const ir::Action &action = actions.at(action_name);
  return action::EvaluateAction(action, entry.action().params(), headers,
                                guard);
}

}  // namespace

gutil::StatusOr<SymbolicTrace> EvaluateTable(
    const Dataplane data_plane, const ir::Table &table,
    const std::vector<pdpi::IrTableEntry> &entries, SymbolicHeaders *headers,
    const z3::expr &guard) {
  // The overall structure describing the match on this table.
  SymbolicTableMatch table_match = EmptyTableMatch(table);
  table_match.matched = Z3Context().bool_val(true);
  const std::string &table_name = table.table_definition().preamble().name();

  // The table semantically is just a bunch of if conditions, one per
  // table entry, we construct this big if-elseif-...-else construct via
  // this simpler representation.
  // Traverse in reverse order: from least to highest priority, since we are
  // building the if-elseif-...-else statement inside out.
  // TODO(babman): sort by priority.
  z3::expr no_row_matched = guard;
  for (int row = entries.size() - 1; row >= 0; row--) {
    const pdpi::IrTableEntry &entry = entries.at(row);
    ASSIGN_OR_RETURN(z3::expr row_match,
                     AnalyzeTableEntryCondition(table, entry, *headers));
    ASSIGN_OR_RETURN(row_match, operators::And(no_row_matched, row_match));
    RETURN_IF_ERROR(AnalyzeTableEntryAction(
        table, entry, data_plane.program.actions(), headers, row_match));

    // Using this alias makes it simpler to put constraints on packet later.
    ASSIGN_OR_RETURN(table_match.matched,
                     operators::Or(table_match.matched, row_match));
    ASSIGN_OR_RETURN(table_match.entry_index,
                     operators::Ite(row_match, Z3Context().int_val(row),
                                    table_match.entry_index));
    // Aggregate the condition for matching on this row with previous guards.
    ASSIGN_OR_RETURN(z3::expr row_missed, operators::Not(row_match));
    ASSIGN_OR_RETURN(no_row_matched,
                     operators::And(no_row_matched, row_missed));
  }

  // Finally, do the default entry. The guard is the negation of all previously
  // evaluated entries guards.
  pdpi::IrTableEntry default_entry;
  default_entry.mutable_action()->set_name(
      table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(
        *(default_entry.mutable_action()->add_params()->mutable_value()),
        util::StringToIrValue(parameter_value));
  }
  RETURN_IF_ERROR(AnalyzeTableEntryAction(table, default_entry,
                                          data_plane.program.actions(), headers,
                                          no_row_matched));

  // This table has been completely evaluated, the result of the evaluation
  // is now in "headers" and "table_match".
  // Time to evaluate the next control construct.
  std::string next_control;
  bool first = true;
  // We only support tables that always have the same next control construct
  // regardless of the table's matches.
  for (const auto &[_, control] :
       table.table_implementation().action_to_next_control()) {
    if (first) {
      next_control = control;
      continue;
    }
    if (next_control != control) {
      return absl::UnimplementedError(absl::StrCat(
          "Table \"", table_name,
          "\" invokes different control constructs based on matched actions."));
    }
  }

  // Evaluate the next control.
  ASSIGN_OR_RETURN(
      SymbolicTrace result,
      control::EvaluateControl(data_plane, next_control, headers, guard));

  // Add this table's match to the trace, and return it.
  // Mark the packet as dropped if this table ends up dropping it.
  result.matched_entries.at(table_name) = table_match;
  return result;
}

SymbolicTableMatch EmptyTableMatch(const ir::Table &table) {
  return {
      Z3Context().bool_val(false),  // No match yet!
      Z3Context().int_val(-1),      // No match index.
      Z3Context().int_val(-1)       // TODO(babman): bitvector.
  };
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
