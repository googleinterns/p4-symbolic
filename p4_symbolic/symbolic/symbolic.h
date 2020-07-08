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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#ifndef P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
#define P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "z3++.h"  // TODO(babman): added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

// Specifies what a packet essentially looks like.
// A concrete output packet within a concrete context produced by our solver
// will be of this type.
struct ConcreteHeader {
  // TODO(babman): add the remaining headers and switch ints to bits.
  int eth_src;
  int eth_dst;
  int eth_type;
};

// Provides symbolic handles for the fields of the symbolic packet used by
// our solver. These handles can be used to contstrain the conrete output
// packets.
struct SymbolicHeader {
  z3::expr eth_src;
  z3::expr eth_Dst;
  z3::expr eth_type;
};

// Expresses a concrete match for a corresponding concrete packet with a
// table in the program.
struct ConcreteTableMatch {
  bool matched;  // false if no entry in this table was matched, true otherwise.
  // if matched is false, these two fields are set to -1.
  int entry_index;  // <concrete_state>[<table_name>] = <entry that was matched>
  int value;
};

// Exposes a symbolic handle for every table entry being hit (by index).
// e.g. for some table "<table_name>"
// <symbolic_table_match>[i] = <concret_state>[<table_name>][i] was matched/hit.
using SymbolicTableMatch = std::vector<z3::expr>;

// Specifies the expected trace in the program that the corresponding
// concrete packet is expected to take.
struct ConcreteTrace {
  std::unordered_map<std::string, ConcreteTableMatch> matched_entries;
  // Can be extended more in the future to include useful
  // flags about dropping the packet, taking specific code (e.g. if)
  // branches, vrf, other interesting events, etc.
};

// Provides symbolic handles for the trace the symbolic packet is constrained
// to take in the program.
struct SymbolicTrace {
  std::unordered_map<std::string, SymbolicTableMatch> matched_entries;
};

// The result of solving the symbolic state with some assertion.
// This contains an input test packet, with its predicted flow in the program,
// and the predicted output.
struct ConcreteContext {
  int ingress_port;
  int egress_port;
  ConcreteHeader ingress_packet;  // Input packet into the program/switch.
  ConcreteHeader egress_packet;  // Expected output packet.
  ConcreteTrace trace;  // Expected trace in the program.
};

// The symbolic context within our analysis.
// Exposes symbolic handles for the fields of the input packet,
// and its trace in the program.
// Assertions are defined on a symbolic context.
struct SymbolicContext {
  z3::expr ingress_port;
  z3::expr egress_port;
  SymbolicHeader ingress_packet;
  SymbolicHeader egress_packet;
  SymbolicTrace trace;
};

// Maps the name of a table to a list of its entries.
// Used as input to our symbolic pipeline.
using ConcreteState =
    std::unordered_map<std::string, std::vector<ir::TableEntry>>;

// The overall state of our symbolic analysis.
// This is returned by our main analysis/interpration function, and is used
// to find concrete test packets and for debugging.
// This is internal to our solver code. External code that uses our solver
// is not expected to access any of these fields or modify them.
struct SymbolicState {
  // The IR represnetation of the p4 program being analyzed.
  ir::P4Program program;
  // The symbolic context of our interpretation/analysis of the program,
  // including symbolic handles on packet headers and its trace.
  SymbolicContext context;
  // Having the z3 solver defined here allows Z3 to remember interesting
  // deductions it made while solving for one particular assertion, and re-use
  // them during solving with future assertions.
  std::unique_ptr<z3::solver> solver;
};

// An assertion is a user defined function that takes a symbolic context
// as input, and returns constraints on symbolic handles exposed by that
// context. For example:
// z3::expr portIsOne(const SymbolicContext &ctx) {
//   return ctx.ingress_port == 1;
// }
using Assertion = std::function<z3::expr(const SymbolicContext&)>;

// Symbolically runs/interprets the given program against the given
// entries for every table in that program, and the available physical ports
// on the switch.
pdpi::StatusOr<SymbolicState> RunP4Pipeline(
    const ir::P4Program &program, const ConcreteState &table_entries,
    const std::vector<int> &physical_ports);

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by symbolic_state.
pdpi::StatusOr<ConcreteContext> Solve(const SymbolicState &symbolic_state,
                                      const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const SymbolicState &symbolic_state);

// clean up Z3 internal memory datastructures, Z3 can still be
// used after this, as if Z3 has been freshly loaded.
// https://github.com/Z3Prover/z3/issues/157
void CleanUpMemory();

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
