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

#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {

pdpi::StatusOr<SolverState *> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports) {
  // Context to use for defining z3 variables, etc..
  z3::context *z3_context = new z3::context();

  // Construct an unconstrainted (free) SymbolicContext.
  SymbolicContext symbolic_context = util::FreeSymbolicContext(z3_context);

  // Construct solver state for this program.
  SolverState *solver_state =
      new SolverState{data_plane.program, data_plane.entries, symbolic_context,
                      std::unique_ptr<z3::solver>(new z3::solver(*z3_context)),
                      std::unique_ptr<z3::context>(z3_context)};

  // Restrict ports to the available physical ports.
  z3::expr ingress_port_domain = z3_context->bool_val(false);
  z3::expr egress_port_domain = z3_context->bool_val(false);
  for (int port : physical_ports) {
    ingress_port_domain =
        ingress_port_domain || symbolic_context.ingress_port == port;
    egress_port_domain =
        egress_port_domain || symbolic_context.egress_port == port;
  }
  solver_state->solver->add(ingress_port_domain);
  solver_state->solver->add(egress_port_domain);

  // Visit tables and find their symbolic matches (and their actions).
  for (const auto &[name, table] : data_plane.program.tables()) {
  }

  return solver_state;
}

pdpi::StatusOr<ConcreteContext> Solve(SolverState *solver_state,
                                      const Assertion &assertion) {
  z3::expr constraint = assertion(solver_state->context);

  solver_state->solver->push();
  solver_state->solver->add(constraint);
  switch (solver_state->solver->check()) {
    case z3::unsat:
      solver_state->solver->pop();
      return absl::Status(absl::StatusCode::kInvalidArgument,
                          "Assertion and program are unsat!");

    case z3::unknown:
      solver_state->solver->pop();
      return absl::Status(absl::StatusCode::kInvalidArgument,
                          "Z3 cannot find satisifying packet model!");

    case z3::sat:
    default:
      z3::model packet_model = solver_state->solver->get_model();
      ConcreteContext result =
          util::ExtractFromModel(solver_state->context, packet_model);
      solver_state->solver->pop();
      return result;
  }
}

std::string DebugSMT(SolverState *solver_state) {
  return solver_state->solver->to_smt2();
}

}  // namespace symbolic
}  // namespace p4_symbolic
