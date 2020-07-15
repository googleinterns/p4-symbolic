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

#include <utility>

#include "p4_symbolic/symbolic/table.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {

z3::context &Z3Context() {
  static z3::context *z3_context = new z3::context();
  return *z3_context;
}

pdpi::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports) {
  // Use global context to define a solver.
  std::unique_ptr<z3::solver> z3_solver =
      std::make_unique<z3::solver>(Z3Context());

  // "Accumulator"-style state used to evaluate tables.
  // Initially free/unconstrained and contains symbolic variables for
  // every input metadata and header field.
  SymbolicPerPacketState symbolic_state = util::FreeSymbolicPacketState();
  z3::expr ingress_port =
      symbolic_state.metadata.at("standard_metadata.ingress_port");
  SymbolicHeader ingress_packet = symbolic_state.header;

  // Restrict ports to the available physical ports.
  z3::expr ingress_port_domain = Z3Context().bool_val(false);
  for (int port : physical_ports) {
    ingress_port_domain = ingress_port_domain || ingress_port == port;
  }
  z3_solver->add(ingress_port_domain);

  // An (initially) empty trace.
  SymbolicTrace trace = {std::unordered_map<std::string, SymbolicTableMatch>(),
                         Z3Context().bool_val(false)};

  // Visit tables and find their symbolic matches (and their actions).
  for (const auto &[name, table] : data_plane.program.tables()) {
    ASSIGN_OR_RETURN(
        table::SymbolicPerPacketStateAndMatch state_and_match,
        table::EvaluateTable(table, data_plane.entries.at(name),
                             data_plane.program.actions(), symbolic_state));

    // Update accumulator state and matches.
    symbolic_state = state_and_match.state;
    trace.matched_entries.insert({name, state_and_match.match});
    trace.dropped = trace.dropped || !state_and_match.match.matched;
  }

  // Construct a symbolic context, containing state and trace information
  // from evaluating the tables.
  z3::expr egress_port =
      symbolic_state.metadata.at("standard_metadata.egress_spec");
  SymbolicHeader egress_packet = symbolic_state.header;
  SymbolicMetadata metadata = symbolic_state.metadata;
  SymbolicContext symbolic_context = {ingress_port,   egress_port,
                                      ingress_packet, egress_packet,
                                      metadata,       trace};

  // Construct solver state for this program.
  return std::make_unique<SolverState>(data_plane.program, data_plane.entries,
                                       symbolic_context, std::move(z3_solver));
}

pdpi::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion) {
  z3::expr constraint = assertion(solver_state->context);

  solver_state->solver->push();
  solver_state->solver->add(constraint);
  switch (solver_state->solver->check()) {
    case z3::unsat:
      solver_state->solver->pop();
      return std::optional<ConcreteContext>();

    case z3::unknown:
      solver_state->solver->pop();
      return std::optional<ConcreteContext>();

    case z3::sat:
    default:
      z3::model packet_model = solver_state->solver->get_model();
      ConcreteContext result =
          util::ExtractFromModel(solver_state->context, packet_model);
      solver_state->solver->pop();
      return std::make_optional<ConcreteContext>(result);
  }
}

std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion) {
  solver_state->solver->push();
  solver_state->solver->add(assertion(solver_state->context));
  std::string smt = solver_state->solver->to_smt2();
  solver_state->solver->pop();
  return smt;
}

}  // namespace symbolic
}  // namespace p4_symbolic
