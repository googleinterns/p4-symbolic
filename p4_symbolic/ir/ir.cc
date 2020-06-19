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

// TODO(babman): Make error messages include more context (e.g. the value
//               of the unsupported expression).
// TODO(babman): Use consistent style when populating protobuf.
//               The best one seems to be using .mutable_<next_field>
//               and passing the returned pointer to the next function.
//               This should avoid new, memory managment, copies.
//               This also will make all the functions (except the main one)
//               return plain absl::Status. Main function should return a
//               StatusOr with a pointer or a reference (?) to avoid copy.

#include "p4_symbolic/ir/ir.h"

#include <string>
#include <unordered_map>

#include "google/protobuf/struct.pb.h"

namespace p4_symbolic {
namespace ir {

// Parsing and validating Headers.
absl::Status ValidateHeaderTypeFields(const google::protobuf::ListValue &list) {
  // Size must be 3.
  int size = list.values_size();
  if (size != 3) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "Headertype fields are badly formatted!");
  }

  // Array must contain [string, int, bool] in that order.
  if (list.values(0).kind_case() != google::protobuf::Value::kStringValue ||
      list.values(1).kind_case() != google::protobuf::Value::kNumberValue ||
      list.values(2).kind_case() != google::protobuf::Value::kBoolValue) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "Headertype fields are badly formatted!");
  }

  return absl::OkStatus();
}

pdpi::StatusOr<HeaderType> TransformHeader(const bmv2::HeaderType &header) {
  HeaderType output;
  output.set_name(header.name());
  output.set_id(header.id());

  for (int i = 0; i < header.fields_size(); i++) {
    const google::protobuf::ListValue &unparsed_field = header.fields(i);
    RETURN_IF_ERROR(ValidateHeaderTypeFields(unparsed_field));

    HeaderField field;
    field.set_name(unparsed_field.values(0).string_value());
    field.set_bitwidth(
        static_cast<int>(unparsed_field.values(1).number_value()));
    field.set_signed_(unparsed_field.values(2).bool_value());
    field.set_header_type(header.name());
    (*output.mutable_fields())[unparsed_field.values(0).string_value()] = field;
  }

  return output;
}

// Parsing values.
absl::Status TransformLValue(google::protobuf::Value bmv2_value,
                             std::string variables[], LValue *dst) {
  // Either a field value or a variable.
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "Left-hand of assignment is badly formatted!");
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  if (type == "field") {
    google::protobuf::ListValue names =
        struct_value.fields().at("value").list_value();

    FieldValue *field_value = dst->mutable_field_value();
    field_value->set_header_name(names.values(0).string_value());
    field_value->set_field_name(names.values(1).string_value());
  } else if (type == "runtime_data") {
    int variable_index =
        static_cast<int>(struct_value.fields().at("value").number_value());

    Variable *variable = dst->mutable_variable_value();
    variable->set_name(variables[variable_index]);
  } else {
    return absl::Status(absl::StatusCode::kUnimplemented,
                        "Unsupported expression in left-hand of assignment!");
  }

  return absl::OkStatus();
}

absl::Status TransformRValue(google::protobuf::Value bmv2_value,
                             std::string variables[], RValue *dst) {
  // TODO(babman): Code duplication between this and TransformLValue.
  //               This function will have more cases later when the
  //               second todo is handled, but we still need to reduce
  //               code duplication.
  //               Difficulty: the type here is RValue instead of LValue.
  //               Possible solution: create piece wise re-usable functions
  //               that return FieldValue/Variable etc, cons: does not reduce
  //               duplicates by much..
  //               Will look at this later.
  // TODO(babman): Support the remaining cases: literals and simple expressions.
  if (bmv2_value.kind_case() != google::protobuf::Value::kStructValue) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "Left-hand of assignment is badly formatted!");
  }

  const google::protobuf::Struct &struct_value = bmv2_value.struct_value();
  const std::string &type = struct_value.fields().at("type").string_value();
  if (type == "field") {
    google::protobuf::ListValue names =
        struct_value.fields().at("value").list_value();

    FieldValue *field_value = dst->mutable_field_value();
    field_value->set_header_name(names.values(0).string_value());
    field_value->set_field_name(names.values(1).string_value());
  } else if (type == "runtime_data") {
    int variable_index =
        static_cast<int>(struct_value.fields().at("value").number_value());

    Variable *variable = dst->mutable_variable_value();
    variable->set_name(variables[variable_index]);
  } else {
    return absl::Status(absl::StatusCode::kUnimplemented,
                        "Unsupported expression in left-hand of assignment!");
  }

  return absl::OkStatus();
}

// Parsing and validating actions.
pdpi::StatusOr<Action> TransformAction(
    const bmv2::Action &bmv2_action,
    const pdpi::ir::IrActionDefinition &pdpi_action) {
  ActionImplementation *action_impl = new ActionImplementation();

  // BMV2 format uses ints as ids for variables.
  // We will replace the ids with the actual variable name.
  std::string *variable_map = new std::string[bmv2_action.runtime_data_size()];
  for (int i = 0; i < bmv2_action.runtime_data_size(); i++) {
    const bmv2::VariableDefinition variable = bmv2_action.runtime_data(i);
    (*action_impl->mutable_variables())[variable.name()] = variable.bitwidth();
    variable_map[i] = variable.name();
  }

  // Parse every statement in body.
  // When encoutering a variable, look it up in the variable map.
  for (int i = 0; i < bmv2_action.primitives_size(); i++) {
    const google::protobuf::Struct &primitive = bmv2_action.primitives(i);
    const std::string &op = primitive.fields().at("op").string_value();
    // TODO(babman): Maybe bring back the enum and use switch-case here? discuss
    // TODO(babman): As we add more statements, this will get more complicated.
    //               It may deserve its own function or file.
    Statement *statement = action_impl->add_action_body();
    if (op == "assign") {
      AssignmentStatement *assignment = statement->mutable_assignment();
      const google::protobuf::Value &params =
          primitive.fields().at("parameters");
      if (params.kind_case() != google::protobuf::Value::kListValue ||
          params.list_value().values_size() != 2) {
        return absl::Status(absl::StatusCode::kInvalidArgument,
                            "Assignment parameters are badly formatted!");
      }

      RETURN_IF_ERROR(TransformLValue(params.list_value().values(0),
                                      variable_map,
                                      assignment->mutable_left()));
      RETURN_IF_ERROR(TransformRValue(params.list_value().values(1),
                                      variable_map,
                                      assignment->mutable_right()));
    } else {
      return absl::Status(absl::StatusCode::kUnimplemented,
                          "Unsupported primitive in action body!");
    }

    // Parse source_info struct into its own protobuf.
    // Applies to all types of statements.
    std::string source_info;
    primitive.fields().at("source_info").SerializeToString(&source_info);
    statement->mutable_source_info()->ParseFromString(source_info);
  }

  // Create the final output and return it.
  Action output;
  output.mutable_action_definition()->CopyFrom(pdpi_action);
  output.set_allocated_action_implementation(action_impl);
  return output;
}

// Parsing and validating tables.
pdpi::StatusOr<Table> TransformTable(
    const bmv2::Table &bmv2_table,
    const pdpi::ir::IrTableDefinition &pdpi_table) {
  TableImplementation *table_impl = new TableImplementation();
  table_impl->set_match_type(bmv2_table.match_type());
  table_impl->set_action_selector_type(bmv2_table.type());

  Table output;
  output.mutable_table_definition()->CopyFrom(pdpi_table);
  output.set_allocated_table_implementation(table_impl);
  return output;
}

// Main transformation function.
pdpi::StatusOr<P4Program *> TransformToIr(const bmv2::P4Program &bmv2,
                                          const pdpi::ir::IrP4Info &pdpi) {
  P4Program *output = new P4Program();

  // Transform headers.
  for (int i = 0; i < bmv2.header_types_size(); i++) {
    const bmv2::HeaderType &unparsed_header = bmv2.header_types(i);
    ASSIGN_OR_RETURN(HeaderType parsed_header,
                     TransformHeader(unparsed_header));
    (*output->mutable_headers())[unparsed_header.name()] = parsed_header;
  }

  // In reality, pdpi.actions_by_name is keyed on aliases and
  // not fully qualified names.
  std::unordered_map<std::string, pdpi::ir::IrActionDefinition>
      actions_by_qualified_name;
  const auto &pdpi_actions = pdpi.actions_by_name();
  for (auto it = pdpi_actions.begin(); it != pdpi_actions.end(); it++) {
    const std::string &name = it->second.preamble().name();
    actions_by_qualified_name[name] = it->second;
  }

  // Transform actions.
  for (int i = 0; i < bmv2.actions_size(); i++) {
    const bmv2::Action &bmv2_action = bmv2.actions(i);
    const std::string &action_name = bmv2_action.name();

    // Matching action must exist in p4info and thus pdpi.
    if (actions_by_qualified_name.count(action_name) != 1) {
      return absl::Status(absl::StatusCode::kInvalidArgument,
                          "BMV2 action missing from p4info!");
    }
    const pdpi::ir::IrActionDefinition &pdpi_action =
        actions_by_qualified_name.at(action_name);  // Safe, no exception.

    ASSIGN_OR_RETURN(
        (*output->mutable_actions())[pdpi_action.preamble().name()],
        TransformAction(bmv2_action, pdpi_action));
  }

  // Similarly, pdpi.tables_by_name is keyed on aliases.
  std::unordered_map<std::string, pdpi::ir::IrTableDefinition>
      tables_by_qualified_name;
  const auto &pdpi_tables = pdpi.tables_by_name();
  for (auto it = pdpi_tables.begin(); it != pdpi_tables.end(); it++) {
    const std::string &name = it->second.preamble().name();
    tables_by_qualified_name[name] = it->second;
  }

  // Transform actions.
  for (int i = 0; i < bmv2.pipelines_size(); i++) {
    for (int j = 0; j < bmv2.pipelines(i).tables_size(); j++) {
      const bmv2::Table &bmv2_table = bmv2.pipelines(i).tables(j);
      const std::string &table_name = bmv2_table.name();

      // Matching action must exist in p4info and thus pdpi.
      if (tables_by_qualified_name.count(table_name) != 1) {
        return absl::Status(absl::StatusCode::kInvalidArgument,
                            "BMV2 table missing from p4info!");
      }
      const pdpi::ir::IrTableDefinition &pdpi_table =
          tables_by_qualified_name.at(table_name);  // Safe, no exception.

      ASSIGN_OR_RETURN(
          (*output->mutable_tables())[pdpi_table.preamble().name()],
          TransformTable(bmv2_table, pdpi_table));
    }
  }

  // Find init_table.
  if (bmv2.pipelines_size() < 1) {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        "BMV2 file contains no pipelines!");
  }
  output->set_initial_table(bmv2.pipelines(0).init_table());

  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
