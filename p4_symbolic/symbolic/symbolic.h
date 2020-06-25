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

#ifndef P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
#define P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_

#include <string>
#include <unordered_map>
#include <vector>

#include "z3++.h"  // added as a system dependency for now.

#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace symbolic {

class Analyzer {
 protected:
  const ir::P4Program &program;
  z3::context context;

  // Maps header fields full names to their corresponding symbolic expression.
  // A header field name is on the form <header_type_name>.<field_name>.
  std::unordered_map<std::string, z3::expr> fields_map;

  // Maps variable full names to their corresponding symbolic expression.
  // A variable full name is on the form <action_full_name>.<variable_name>,
  // where action is the enclosing action in which the variable was defined.
  std::unordered_map<std::string, z3::expr> variables_map;

  // Maps a table full name to the corresponding symbolic expressions
  // representing that an entry in that table was matched.
  // The expressions are stored as a vector matching the table entries by index,
  // such that: entries_map['table1'][i] <=> row i in table1 was hit.
  std::unordered_map<std::string, std::vector<z3::expr>> entries_map;

  // Header related functions.
  void AnalyzeHeaderType(const ir::HeaderType&);
  void AnalyzeHeaderField(const ir::HeaderField&, const string&);

  // Table related functions.
  void AnalyzeTable(const ir::Table&);

  // Action, statements, and expressions.
  void AnalyzeAction(const ir::Action&);
  void AnalyzeStatement(const ir::Statement&, const string&);
  void AnalyzeAssignmentStatement(const ir::AssignmentStatement&, const string&);
  void AnalyzeLValue(const ir::LValue&, const string&);
  void AnalyzeRValue(const ir::RValue&, const string&);
  void AnalyzeFieldValue(const ir::FieldValue&, const string&);
  void AnalyzeVariable(const ir::Variable&, const string&);
  
 public:
  Analyzer() = default;

  // Class is not copyable or movable.
  Analyzer(const Analyzer&) = delete;
  Analyzer& operator=(const Analyzer&) = delete;
  Analyzer(Analyzer&&) = delete;
  Analyzer& operator=(Analyzer&&) = delete;

  // Entry point
  void Analyze(const ir::P4Program&);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
