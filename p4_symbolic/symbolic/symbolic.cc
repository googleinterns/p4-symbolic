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

#include <memory>

#include "absl/strings/str_format.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/names.h"
#include "p4_symbolic/symbolic/table.h"

namespace p4_symbolic {
namespace symbolic {

pdpi::StatusOr<SolverState> AnalyzeProgram(const ir::P4Program &program) {
  // construct solver state for this program and the given context.
  SolverState solver_state;
  solver_state.program = program;
  solver_state.context = std::unique_ptr<z3::context>(new z3::context());
  solver_state.solver =
      std::unique_ptr<z3::solver>(new z3::solver(*solver_state.context));

  // Visit actions first to define symbolic expressions for their parameters.
  // Then visit tables, since their entries will use the action parameters
  // symbolic expressions.
  // TODO(babman): ensure this order is fine for more complex workflows,
  //               e.g. VRF, we may need to traverse actions + tables in order,
  //               starting from init_table?
  // TODO(babman): On second thought, I think this is ok, provided that we
  //               create placeholder symbolic traces for actions prior to
  //               fully analyzing them. This way an action calling another
  //               action is guaranteed to find a symbolic trace for it to
  //               instantiate regardless of analysis order.
  for (const auto &[action_name, action] : program.actions()) {
    ASSIGN_OR_RETURN(ActionSymbolicTrace action_trace,
                     action::AnalyzeAction(action, solver_state));
    solver_state.action_map.insert({action_name, action_trace});
  }
  for (const auto &[_, table] : program.tables()) {
    ASSIGN_OR_RETURN(z3::expr table_expression,
                     table::AnalyzeTable(table, solver_state));
    solver_state.solver->add(table_expression);
  }

  return solver_state;
}

std::string DebugSMT(const SolverState &solver_state) {
  return solver_state.solver->to_smt2();
}

pdpi::StatusOr<Packet> FindPacketMatching(const SolverState &solver_state,
                                          const std::string &table, int row) {
  // TODO(babman): Negate higher priority matches after sorting, see table.cc.
  solver_state.solver->push();
  z3::expr entry_alias = solver_state.context->bool_const(
      names::ForTableEntry(table, row).c_str());
  solver_state.solver->add(entry_alias);

  switch (solver_state.solver->check()) {
    case z3::unsat:
      solver_state.solver->pop();
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Table %s and row %d is impossible to hit", table,
                          row));

    case z3::unknown:
      solver_state.solver->pop();
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrFormat("Could not find packet to hit Table %s and row %d",
                          table, row));

    case z3::sat:
    default:
      z3::model packet_model = solver_state.solver->get_model();
      std::map<std::string, std::string> output;
      for (unsigned int i = 0; i < packet_model.size(); i++) {
        z3::func_decl field_declaration = packet_model[i];
        if (!field_declaration.is_const()) {
          continue;
        }
        output[field_declaration.to_string()] =
            packet_model.get_const_interp(field_declaration).to_string();
      }

      solver_state.solver->pop();
      return output;
  }
}

void CleanUpMemory() { Z3_finalize_memory(); }

}  // namespace symbolic
}  // namespace p4_symbolic
