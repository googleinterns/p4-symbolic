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

// Contains the entry point to our symbolic analysis code, as well
// as helpers for debugging and finding concrete packets.

#ifndef P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
#define P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_

#include <map>
#include <string>

#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/structs.h"
#include "z3++.h"  // TODO(babman): added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

// Maps packet field name to its concrete value.
// e.g. "metadata.ingress_port" to 1.
using Packet = std::map<std::string, std::string>;

// Symbolically Analyzes the given program, generating z3 symbolic expressions
// and that are later solved to produce concerete packets.
pdpi::StatusOr<SolverState> AnalyzeProgram(const ir::P4Program &program);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const SolverState &solver_state);

// Finds a concrete packet matching the given table and table entry index.
pdpi::StatusOr<Packet> FindPacketMatching(const SolverState &solver_state,
                                          const std::string &table, int row);

// clean up Z3 internal memory datastructures, Z3 can still be
// used after this, as if Z3 has been freshly loaded.
// https://github.com/Z3Prover/z3/issues/157
void CleanUpMemory();

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
