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
#include "p4_symbolic/symbolic/typed.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {
namespace table {

namespace {

// Analyze a single match that is part of a table entry.
// Constructs a symbolic expression that semantically corresponds to this
// match.
gutil::StatusOr<TypedExpr> AnalyzeSingleMatch(
    p4::config::v1::MatchField match_definition,
    const TypedExpr &field_expression, const pdpi::IrMatch &match) {
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
      ASSIGN_OR_RETURN(TypedExpr value_expression,
                       util::IrValueToZ3Expr(match.exact()));
      return field_expression == value_expression;
    }
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Found unsupported match type ", match_definition.DebugString()));
  }
}

// Constructs a symbolic expression that is true if and only if this entry
// is matched on.
gutil::StatusOr<TypedExpr> AnalyzeTableEntryCondition(
    const ir::Table &table, const pdpi::IrTableEntry &entry,
    const SymbolicHeaders &headers) {
  // Make sure number of match keys is the same in the table definition and
  // table entry.
  if (table.table_definition().match_fields_by_id_size() !=
      entry.matches_size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Found a match entry ", entry.DebugString(), " in table",
                     table.table_definition().preamble().name(),
                     " with wrong match fields count"));
  }

  // Construct the match condition expression.
  TypedExpr condition_expression = TypedExpr(Z3Context().bool_val(true));
  for (const auto &[id, match_fields] :
       table.table_definition().match_fields_by_id()) {
    p4::config::v1::MatchField match_definition = match_fields.match_field();

    // Match id is unique only within the enclosing table.
    // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
    // Match id starts at 1, and proceeds in the same order the matches are
    // defined in, which is identical to the order they are provided by in
    // the table entries file.
    const pdpi::IrMatch &match = entry.matches(id - 1);

    // TODO(babman): We should put in the expression of the match from bmv2
    //               json in the IR, and use instead of the name.
    //               @konne mentioned this before in a meeting.
    const std::string &match_string_expression = match_definition.name();
    if (headers.count(match_string_expression) != 1) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unknown table match expression ", match_string_expression,
          " in table ", table.table_definition().preamble().name()));
    }
    ASSIGN_OR_RETURN(
        TypedExpr match_expression,
        AnalyzeSingleMatch(match_definition,
                           headers.at(match_string_expression), match));
    condition_expression = condition_expression && match_expression;
  }

  return condition_expression;
}

// Constructs a symbolic expressions that represents the action invocation
// corresponding to this entry.
gutil::StatusOr<SymbolicHeaders> AnalyzeTableEntryAction(
    const ir::Table &table, const pdpi::IrTableEntry &entry,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    const SymbolicHeaders &headers) {
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
  return action::EvaluateAction(action, entry.action().params(), headers);
}

}  // namespace

gutil::StatusOr<SymbolicHeadersAndTableMatch> EvaluateTable(
    const ir::Table &table, const std::vector<pdpi::IrTableEntry> &entries,
    const google::protobuf::Map<std::string, ir::Action> &actions,
    const SymbolicHeaders &headers) {
  // The overall structure describing the match on this table.
  SymbolicTableMatch table_match = {
      TypedExpr(Z3Context().bool_val(false)),  // No match yet!
      TypedExpr(Z3Context().int_val(-1)),      // No match index.
      TypedExpr(Z3Context().int_val(-1))       // TODO(babman): bitvector.
  };

  // Begin with the default entry.
  pdpi::IrTableEntry default_entry;
  default_entry.mutable_action()->set_name(
      table.table_implementation().default_action());
  for (const std::string &parameter_value :
       table.table_implementation().default_action_parameters()) {
    ASSIGN_OR_RETURN(
        *(default_entry.mutable_action()->add_params()->mutable_value()),
        util::StringToIrValue(parameter_value));
  }
  ASSIGN_OR_RETURN(
      SymbolicHeaders modified_headers,
      AnalyzeTableEntryAction(table, default_entry, actions, headers));

  // The table semantically is just a bunch of if conditions, one per
  // table entry, we construct this big if-elseif-...-else construct via
  // this simpler representation.
  // Traverse in reverse order: from least to highest priority, since we are
  // building the if-elseif-...-else statement inside out.
  for (int row = entries.size() - 1; row >= 0; row--) {
    const pdpi::IrTableEntry &entry = entries.at(row);
    ASSIGN_OR_RETURN(TypedExpr row_match,
                     AnalyzeTableEntryCondition(table, entry, headers));
    ASSIGN_OR_RETURN(SymbolicHeaders row_headers,
                     AnalyzeTableEntryAction(table, entry, actions, headers));

    // Using this alias makes it simpler to put constraints on packet later.
    table_match.matched = table_match.matched || row_match;
    table_match.entry_index =
        TypedExpr::ite(row_match, TypedExpr(Z3Context().int_val(row)),
                       table_match.entry_index);

    // Apply the changes to the header fields if the symbolic condition to match
    // on this entry is satisified.
    modified_headers =
        util::MergeHeadersOnCondition(modified_headers, row_headers, row_match);
  }

  return SymbolicHeadersAndTableMatch{modified_headers, table_match};
}

}  // namespace table
}  // namespace symbolic
}  // namespace p4_symbolic
