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

#include <map>
#include <string>
#include <unordered_map>
#include <vector>

#include "absl/status/status.h"
#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "z3++.h"  // added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

class Analyzer {
 protected:
  ir::P4Program kProgram;
  z3::context kContext;

  // Maps header fields full names to their corresponding symbolic expression.
  // A header field name is on the form <header_type_name>.<field_name>.
  std::unordered_map<std::string, z3::expr> kFieldsMap;

  // Maps variable full names to their corresponding symbolic expression.
  // A variable full name is on the form <action_full_name>.<variable_name>,
  // where action is the enclosing action in which the variable was defined.
  std::unordered_map<std::string, z3::expr> kVariablesMap;

  // Maps a table full name and row index to the corresponding symbolic
  // expression representing matching with that row, such that:
  // entries_map['table1_3'] <=> row at index 3 in table1 was hit.
  std::unordered_map<std::string, z3::expr> kEntriesMap;

  // Maps an action full name to the corresponding symbolic expressions
  // representing that this action was indeed matched on and called.
  std::unordered_map<std::string, z3::expr> kActionsMap;

  // Symbolic constraints that describe relationships between various variables
  // and fields in the program.
  std::vector<z3::expr> kConstraints;

  // Header related functions.
  absl::Status AnalyzeHeaderType(const ir::HeaderType&);
  absl::Status AnalyzeHeaderField(const ir::HeaderField&, const std::string&);

  // Table related functions.
  absl::Status AnalyzeTable(const ir::Table&);

  // Actions and statements.
  absl::Status AnalyzeAction(const ir::Action&);
  absl::Status AnalyzeStatement(const ir::Statement&, const z3::expr&,
                                const std::string&);
  absl::Status AnalyzeAssignmentStatement(const ir::AssignmentStatement&,
                                          const z3::expr&, const std::string&);

  // Expressions: these construct a z3 equivalent symbolic expression and
  // return it.
  pdpi::StatusOr<z3::expr*> AnalyzeLValue(const ir::LValue&, const z3::expr&,
                                          const std::string&);
  pdpi::StatusOr<z3::expr*> AnalyzeRValue(const ir::RValue&, const z3::expr&,
                                          const std::string&);
  pdpi::StatusOr<z3::expr*> AnalyzeFieldValue(const ir::FieldValue&,
                                              const z3::expr&,
                                              const std::string&);
  pdpi::StatusOr<z3::expr*> AnalyzeVariable(const ir::Variable&,
                                            const z3::expr&,
                                            const std::string&);

 public:
  Analyzer() = default;
  ~Analyzer() {
    // clean up Z3 internal memory datastructures, Z3 can still be
    // used after this, as if Z3 has been freshly loaded.
    // https://github.com/Z3Prover/z3/issues/157
    Z3_finalize_memory();
  }

  // Class is not copyable or movable.
  Analyzer(const Analyzer&) = delete;
  Analyzer& operator=(const Analyzer&) = delete;
  Analyzer(Analyzer&&) = delete;
  Analyzer& operator=(Analyzer&&) = delete;

  // Entry point
  absl::Status Analyze(ir::P4Program);

  // Dumps the SMT program for debugging.
  std::string DebugSMT();

  // API for finding test packets after analysis.
  pdpi::StatusOr<std::map<std::string, std::string>> FindPacketHittingRow(
      const std::string&, int);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
