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

#include "p4_symbolic/ir/ir.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "absl/strings/str_format.h"
#include "google/protobuf/struct.pb.h"

namespace p4_symbolic {
namespace ir {

namespace {

// Extracting source code information.
pdpi::StatusOr<bmv2::SourceLocation> ExtractSourceLocation(
    google::protobuf::Value unparsed_source_location) {
  if (unparsed_source_location.kind_case() !=
      google::protobuf::Value::kStructValue) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Source Location is expected to be a struct, found %s",
                        unparsed_source_location.DebugString()));
  }

  const auto &fields = unparsed_source_location.struct_value().fields();
  if (fields.count("filename") != 1 || fields.count("line") != 1 ||
      fields.count("column") != 1 || fields.count("source_fragment") != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Source Location is expected to contain 'filename', "
                        "'line', 'colmn', and 'source_fragment, found %s",
                        unparsed_source_location.DebugString()));
  }

  bmv2::SourceLocation output;
  output.set_filename(fields.at("filename").string_value());
  output.set_line(fields.at("line").number_value());
  output.set_column(fields.at("column").number_value());
  output.set_source_fragment(fields.at("source_fragment").string_value());
  return output;
}

// Parsing and validating Headers.
absl::Status ValidateHeaderTypeFields(const google::protobuf::ListValue &list) {
  // Size must be 3.
  int size = list.values_size();
  if (size != 3) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Header field should contain 3 elements, found %s",
                        list.DebugString()));
  }

  // Array must contain [string, int, bool] in that order.
  if (list.values(0).kind_case() != google::protobuf::Value::kStringValue ||
      list.values(1).kind_case() != google::protobuf::Value::kNumberValue ||
      list.values(2).kind_case() != google::protobuf::Value::kBoolValue) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Header field should be [string, int, bool], found %s",
                        list.DebugString()));
  }

  return absl::OkStatus();
}

pdpi::StatusOr<HeaderType> ExtractHeaderType(const bmv2::HeaderType &header) {
  HeaderType output;
  output.set_name(header.name());
  output.set_id(header.id());
  for (const google::protobuf::ListValue &unparsed_field : header.fields()) {
    RETURN_IF_ERROR(ValidateHeaderTypeFields(unparsed_field));

    HeaderField &field =
        (*output.mutable_fields())[unparsed_field.values(0).string_value()];
    field.set_name(unparsed_field.values(0).string_value());
    field.set_bitwidth(unparsed_field.values(1).number_value());
    field.set_signed_(unparsed_field.values(2).bool_value());
    field.set_header_type(header.name());
  }

  return output;
}

// Functions for translating values.
pdpi::StatusOr<LValue> ExtractLValue(
    const google::protobuf::Value &bmv2_value,
    const std::vector<std::string> &variables) {
  LValue output;
  // Either a field value or a variable.
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue ||
      bmv2_value.struct_value().fields().count("type") != 1 ||
      bmv2_value.struct_value().fields().count("value") != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Lvalue must contain 'type' and 'value', found %s",
                        bmv2_value.DebugString()));
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  if (type == "field") {
    const google::protobuf::ListValue &names =
        struct_value.fields().at("value").list_value();

    FieldValue *field_value = output.mutable_field_value();
    field_value->set_header_name(names.values(0).string_value());
    field_value->set_field_name(names.values(1).string_value());
  } else if (type == "runtime_data") {
    int variable_index = struct_value.fields().at("value").number_value();

    Variable *variable = output.mutable_variable_value();
    variable->set_name(variables[variable_index]);
  } else {
    return absl::Status(
        absl::StatusCode::kUnimplemented,
        absl::StrFormat("Unsupported lvalue %s", bmv2_value.DebugString()));
  }

  return output;
}

pdpi::StatusOr<RValue> ExtractRValue(
    const google::protobuf::Value &bmv2_value,
    const std::vector<std::string> &variables) {
  // TODO(babman): Support the remaining cases: literals and simple expressions.
  RValue output;
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue ||
      bmv2_value.struct_value().fields().count("type") != 1 ||
      bmv2_value.struct_value().fields().count("value") != 1) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Rvalue must contain 'type' and 'value', found %s",
                        bmv2_value.DebugString()));
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  if (type == "field") {
    const google::protobuf::ListValue &names =
        struct_value.fields().at("value").list_value();

    FieldValue *field_value = output.mutable_field_value();
    field_value->set_header_name(names.values(0).string_value());
    field_value->set_field_name(names.values(1).string_value());
  } else if (type == "runtime_data") {
    int variable_index = struct_value.fields().at("value").number_value();

    Variable *variable = output.mutable_variable_value();
    variable->set_name(variables[variable_index]);
  } else {
    return absl::Status(
        absl::StatusCode::kUnimplemented,
        absl::StrFormat("Unsupported rvalue %s", bmv2_value.DebugString()));
  }

  return output;
}

// Parsing and validating actions.
pdpi::StatusOr<Action> ExtractAction(
    const bmv2::Action &bmv2_action,
    const pdpi::ir::IrActionDefinition &pdpi_action) {
  Action output;
  // Definition is copied form pdpi.
  output.mutable_action_definition()->CopyFrom(pdpi_action);

  // Implementation is extracted from bmv2.
  ActionImplementation *action_impl = output.mutable_action_implementation();

  // BMV2 format uses ints as ids for variables.
  // We will replace the ids with the actual variable name.
  std::vector<std::string> variable_map(bmv2_action.runtime_data_size());
  for (int i = 0; i < bmv2_action.runtime_data_size(); i++) {
    const bmv2::VariableDefinition variable = bmv2_action.runtime_data(i);
    (*action_impl->mutable_variables())[variable.name()] = variable.bitwidth();
    variable_map[i] = variable.name();
  }

  // Parse every statement in body.
  // When encoutering a variable, look it up in the variable map.
  for (const google::protobuf::Struct &primitive : bmv2_action.primitives()) {
    if (primitive.fields().count("op") != 1 ||
        primitive.fields().count("parameters") != 1) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Primitive statement in action %s should contain 'op'"
                          ", 'parameters', found %s",
                          pdpi_action.preamble().name(),
                          primitive.DebugString()));
    }

    const std::string &operation = primitive.fields().at("op").string_value();
    // TODO(babman): Maybe bring back the enum and use switch-case here? discuss
    Statement *statement = action_impl->add_action_body();
    if (operation == "assign") {
      AssignmentStatement *assignment = statement->mutable_assignment();
      const google::protobuf::Value &params =
          primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() != 2) {
        return absl::Status(
            absl::StatusCode::kInvalidArgument,
            absl::StrFormat("Assignment statement in action %s must contain 2 "
                            "parameters, found %s",
                            pdpi_action.preamble().name(),
                            primitive.DebugString()));
      }

      ASSIGN_OR_RETURN(
          LValue lvalue,
          ExtractLValue(params.list_value().values(0), variable_map));
      ASSIGN_OR_RETURN(
          RValue rvalue,
          ExtractRValue(params.list_value().values(1), variable_map));
      assignment->mutable_left()->CopyFrom(lvalue);
      assignment->mutable_right()->CopyFrom(rvalue);
    } else {
      return absl::Status(
          absl::StatusCode::kUnimplemented,
          absl::StrFormat("Unsupported statement in action %s, found %s",
                          pdpi_action.preamble().name(),
                          primitive.DebugString()));
    }

    // Parse source_info struct into its own protobuf.
    // Applies to all types of statements.
    if (primitive.fields().count("source_info") != 1) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat(
              "Statement in action %s does not have source_info, found %s",
              pdpi_action.preamble().name(), primitive.DebugString()));
    }

    ASSIGN_OR_RETURN(
        bmv2::SourceLocation source_location,
        ExtractSourceLocation(primitive.fields().at("source_info")));
    statement->mutable_source_info()->CopyFrom(source_location);
  }

  return output;
}

// Parsing and validating tables.
pdpi::StatusOr<Table> ExtractTable(
    const bmv2::Table &bmv2_table,
    const pdpi::ir::IrTableDefinition &pdpi_table) {
  Table output;
  // Table definition is copied from pdpi.
  output.mutable_table_definition()->CopyFrom(pdpi_table);

  // Table implementation is extracted from bmv2.
  TableImplementation *table_impl = output.mutable_table_implementation();
  table_impl->set_match_type(bmv2_table.match_type());
  table_impl->set_action_selector_type(bmv2_table.type());

  return output;
}

}  // namespace

// Main Translation function.
pdpi::StatusOr<P4Program> Bmv2AndP4infoToIr(const bmv2::P4Program &bmv2,
                                            const pdpi::ir::IrP4Info &pdpi) {
  P4Program output;

  // Translate headers.
  for (const bmv2::HeaderType &unparsed_header : bmv2.header_types()) {
    ASSIGN_OR_RETURN((*output.mutable_headers())[unparsed_header.name()],
                     ExtractHeaderType(unparsed_header));
  }

  // In reality, pdpi.actions_by_name is keyed on aliases and
  // not fully qualified names.
  std::unordered_map<std::string, const pdpi::ir::IrActionDefinition &>
      actions_by_qualified_name;
  const auto &pdpi_actions = pdpi.actions_by_name();
  for (const auto &it : pdpi_actions) {
    const std::string &name = it.second.preamble().name();
    actions_by_qualified_name.insert({name, it.second});
  }

  // Translate actions.
  for (const bmv2::Action &bmv2_action : bmv2.actions()) {
    const std::string &action_name = bmv2_action.name();

    // Matching action must exist in p4info and thus pdpi.
    if (actions_by_qualified_name.count(action_name) != 1) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Action %s is missing from p4info!", action_name));
    }
    const pdpi::ir::IrActionDefinition &pdpi_action =
        actions_by_qualified_name.at(action_name);  // Safe, no exception.

    ASSIGN_OR_RETURN((*output.mutable_actions())[pdpi_action.preamble().name()],
                     ExtractAction(bmv2_action, pdpi_action));
  }

  // Similarly, pdpi.tables_by_name is keyed on aliases.
  std::unordered_map<std::string, const pdpi::ir::IrTableDefinition &>
      tables_by_qualified_name;
  for (const auto &it : pdpi.tables_by_name()) {
    const std::string &name = it.second.preamble().name();
    tables_by_qualified_name.insert({name, it.second});
  }

  // Translate tables.
  for (const auto &pipeline : bmv2.pipelines()) {
    for (const bmv2::Table &bmv2_table : pipeline.tables()) {
      const std::string &table_name = bmv2_table.name();

      // Matching action must exist in p4info and thus pdpi.
      if (tables_by_qualified_name.count(table_name) != 1) {
        return absl::Status(
            absl::StatusCode::kInvalidArgument,
            absl::StrFormat("Table %s is missing from p4info!", table_name));
      }
      const pdpi::ir::IrTableDefinition &pdpi_table =
          tables_by_qualified_name.at(table_name);  // Safe, no exception.

      ASSIGN_OR_RETURN((*output.mutable_tables())[pdpi_table.preamble().name()],
                       ExtractTable(bmv2_table, pdpi_table));
    }
  }

  // Find init_table.
  if (bmv2.pipelines_size() < 1) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "BMV2 file contains no pipelines!");
  }
  output.set_initial_table(bmv2.pipelines(0).init_table());

  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
