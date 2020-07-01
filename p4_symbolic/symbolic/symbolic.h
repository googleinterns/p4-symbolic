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
#include "z3++.h"  // TODO(babman): added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

// Maps packet field name to its concrete value.
// e.g. "metadata.ingress_port" to 1.
using Packet = std::map<std::string, std::string>;

class Analyzer {
 protected:
  ir::P4Program program_;
  z3::context context_;

  // Maps header fields full names to their corresponding symbolic expression.
  // A header field name is on the form <header_type_name>.<field_name>.
  std::unordered_map<std::string, z3::expr> fields_map_;

  // Maps variable full names to their corresponding symbolic expression.
  // A variable full name is on the form <action_full_name>.<variable_name>,
  // where action is the enclosing action in which the variable was defined.
  std::unordered_map<std::string, z3::expr> variables_map_;

  // Maps a table full name and row index to the corresponding symbolic
  // expression representing matching with that row, such that:
  // entries_map['table1_3'] <=> row at index 3 in table1 was hit.
  std::unordered_map<std::string, z3::expr> entries_map_;

  // Maps an action full name to the corresponding symbolic expressions
  // representing that this action was indeed matched on and called.
  std::unordered_map<std::string, z3::expr> actions_map_;

  // Symbolic constraints that describe relationships between various variables
  // and fields in the program.
  std::vector<z3::expr> constraints_;

  // Header related functions.
  absl::Status AnalyzeHeaderType(const ir::HeaderType &header_type);
  absl::Status AnalyzeHeaderField(const ir::HeaderField &header_field,
                                  const std::string &header_type);

  // Table related functions.
  absl::Status AnalyzeTable(const ir::Table &table);

  // Actions and statements.
  absl::Status AnalyzeAction(const ir::Action &action);
  absl::Status AnalyzeStatement(const ir::Statement &statement,
                                const z3::expr &precondition,
                                const std::string &action);
  absl::Status AnalyzeAssignmentStatement(
      const ir::AssignmentStatement &assignment, const z3::expr &precondition,
      const std::string &action);

  // Expressions: these construct a z3 equivalent symbolic expression and
  // return it.
  pdpi::StatusOr<z3::expr *> AnalyzeLValue(const ir::LValue &lvalue,
                                           const z3::expr &precondition,
                                           const std::string &action);
  pdpi::StatusOr<z3::expr *> AnalyzeRValue(const ir::RValue &rvalue,
                                           const z3::expr &precondition,
                                           const std::string &action);
  pdpi::StatusOr<z3::expr *> AnalyzeFieldValue(
      const ir::FieldValue &field_value, const z3::expr &precondition,
      const std::string &action);
  pdpi::StatusOr<z3::expr *> AnalyzeVariable(const ir::Variable &variable,
                                             const z3::expr &precondition,
                                             const std::string &action);

 public:
  Analyzer() = default;
  ~Analyzer() {
    // clean up Z3 internal memory datastructures, Z3 can still be
    // used after this, as if Z3 has been freshly loaded.
    // https://github.com/Z3Prover/z3/issues/157
    Z3_finalize_memory();
  }

  // Class is not copyable or movable.
  Analyzer(const Analyzer &) = delete;
  Analyzer &operator=(const Analyzer &) = delete;
  Analyzer(Analyzer &&) = delete;
  Analyzer &operator=(Analyzer &&) = delete;

  // Entry point
  absl::Status Analyze(ir::P4Program program);

  // Dumps the SMT program for debugging.
  std::string DebugSMT();

  // API for finding test packets after analysis.
  pdpi::StatusOr<Packet> FindPacketHittingRow(const std::string &table,
                                              int row);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
