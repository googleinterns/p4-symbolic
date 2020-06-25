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

#include "absl/strings/str_format.h"

namespace p4_symbolic {
namespace symbolic {

void Analyzer::Analyze(const ir::P4Program &program) {
  this->program = program;
}

void AnalyzeHeaderType(const ir::HeaderType &header_type) {
  const string &header_type_name = header_type.name();
  for (const auto &[_, header_field] : header_type.fields()) {
    this->AnalyzeHeaderField(header_field, header_type_name);
  }
}

void AnalyzeHeaderField(const ir::HeaderField &header_field,
                        const string &header_type) {
  const string &full_name =
      absl::StrFormat("%s.%s", header_type, header_field.name());
  this->fields_map[full_name] = this->context.int_const(full_name);
}

void AnalyzeTable(const ir::Table &table) {
  const string &table_name = table.table_definition().preamble().name();

  for (const ir::TableEntry &entry : table.table_implementation().entries()) {
    for (const auto &[id, match] : table.table_definition().match_fields_by_id()) {
      // Match id is unique only within the enclosing table.
      // https://github.com/p4lang/p4runtime/blob/master/docs/v1/p4runtime-id-notes.md
      // Match id starts at 1, and proceeds in the same order the matches are
      // defined in, which is identical to the order they are provided by in
      // the table entries file.
      int index = id - 1;  // index of corresponding value in the table entry.
      int value = entry.match_values(index);
    }
    // Start by defining a symbolic expression representing a *potential* match.
    // This is ignoring priorities/overlaps.
    // TODO(babman): Add support for priorities
  }
}

void AnalyzeAction(const ir::Action &action) {
}

void AnalyzeStatement(const ir::Statement &statement,
                      const string &action) {
}

void AnalyzeAssignmentStatement(const ir::AssignmentStatement &assignment,
                                const string &action) {
}

void AnalyzeLValue(const ir::LValue &lvalue,
                   const string &action) {
}

void AnalyzeRValue(const ir::RValue &rvalue,
                   const string &action) {
}

void AnalyzeFieldValue(const ir::FieldValue &field_value,
                       const string &action) {
}

void AnalyzeVariable(const ir::Variable &variable,
                     const string &action) {
}


}  // namespace symbolic
}  // namespace p4_symbolic
