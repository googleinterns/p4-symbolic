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
#include "p4_symbolic/ir/table_entries.h"
#include "z3++.h"  // TODO(babman): added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

// Global pointer to the z3::context used for creating symbolic expressions
// during symbolic evaluation.
// Do not access this from client code. This is completely managed by this file.
// Z3_context is set when EvaluateP4Pipeline is called, and is used by all
// functions nested in that call. It is unset and deleted when the corresponding
// returned SolverState pointer is cleaned.
// Warning: do not call EvaluatP4Pipeline until the state returned by any
// previous call is deleted.
extern z3::context *Z3_CONTEXT;

// Specifies what a packet essentially looks like.
// A concrete output packet within a concrete context produced by our solver
// will be of this type.
struct ConcreteHeader {
  // TODO(babman): Switch to bit string.
  int eth_src;
  int eth_dst;
  int eth_type;

  int outer_ipv4_src;
  int outer_ipv4_dst;
  int outer_ipv6_dst_upper;
  int outer_ipv6_dst_lower;
  int outer_protocol;
  int outer_dscp;
  int outer_ttl;

  int inner_ipv4_dst;
  int inner_ipv6_dst_upper;
  int inner_ipv6_dst_lower;
  int inner_protocol;
  int inner_dscp;
  int inner_ttl;

  int icmp_type;
  int vid;
};

// Maps the name of a metadata field to its concrete value.
// Unlike ConcreteHeader, a metadata field is not part of the physical packet,
// it is a logical value used by the P4 program (e.g. vrf).
// TODO(babman): It is unclear yet if we want to hardcode the names of the
// metadata fields, like we do with concrete header. I am using the most
// flexible option for now, and will be able to better understand this after
// implementing and experimenting with this a bit.
using ConcreteMetadata = std::unordered_map<std::string, int>;

// Provides symbolic handles for the fields of the symbolic packet used by
// our solver. These handles can be used to contstrain the conrete output
// packets.
struct SymbolicHeader {
  // TODO(babman): Swith to bit strings.
  z3::expr eth_src;   // 48 bit.
  z3::expr eth_dst;   // 48 bit.
  z3::expr eth_type;  // 16 bit.

  z3::expr outer_ipv4_src;        // 32 bit, valid if eth_type = 0x0800
  z3::expr outer_ipv4_dst;        // 32 bit, valid if eth_type = 0x0800
  z3::expr outer_ipv6_dst_upper;  // 64 bit, valid if eth_type = 0x86dd
  z3::expr outer_ipv6_dst_lower;  // 64 bit, valid if eth_type = 0x86dd
  z3::expr outer_protocol;        // 8 bit, valid if eth_type is ip
  z3::expr outer_dscp;            // 6 bit, valid if eth_type is ip
  z3::expr outer_ttl;             // 8 bit, valid if eth_type is ip

  z3::expr inner_ipv4_dst;        // 32 bit, valid if outer_protocol = 4
  z3::expr inner_ipv6_dst_upper;  // 64 bit, valid if outer_protocol = 4
  z3::expr inner_ipv6_dst_lower;  // 64 bit, valid if outer_protocol = 41
  z3::expr inner_protocol;        // 8 bit, valid if outer_protocol = 4/41
  z3::expr inner_dscp;            // 6 bit, valid if outer_protocol = 4/41
  z3::expr inner_ttl;             // 8 bit, valid if outer_protocol = 4/41

  z3::expr icmp_type;  // 8 bit, valid if eth_type is ip
  z3::expr vid;        // 12 bit, valid if eth_type = 0x6007
};

// The symbolic counterpart of ConcreteMetadata. This can be used to constrain
// intermediate values.
using SymbolicMetadata = std::unordered_map<std::string, z3::expr>;

// Expresses a concrete match for a corresponding concrete packet with a
// table in the program.
struct ConcreteTableMatch {
  bool matched;  // false if no entry in this table was matched, true otherwise.
  // if matched is false, these two fields are set to -1.
  int entry_index;
  int value;
};

// Exposes a symbolic handle for a match between the symbolic packet and
// a symbolic table.
// This allows encoding of constraints on which (if any) entries are matched,
// and the value of the match.
// e.g. for some table "<table_name>":
// 1. (<symbolic_table_match>.entry_index == i) iff
//    <entries>[<table_name>][i] was matched/hit.
struct SymbolicTableMatch {
  z3::expr matched;
  z3::expr entry_index;
  z3::expr value;
};

// Specifies the expected trace in the program that the corresponding
// concrete packet is expected to take.
struct ConcreteTrace {
  std::unordered_map<std::string, ConcreteTableMatch> matched_entries;
  // Can be extended more in the future to include useful
  // flags about dropping the packet, taking specific code (e.g. if)
  // branches, vrf, other interesting events, etc.
  bool dropped;  // true if the packet was dropped.
};

// Provides symbolic handles for the trace the symbolic packet is constrained
// to take in the program.
struct SymbolicTrace {
  std::unordered_map<std::string, SymbolicTableMatch> matched_entries;
  z3::expr dropped;
};

// The result of solving with some assertion.
// This contains an input test packet with its predicted flow in the program,
// and the predicted output.
struct ConcreteContext {
  int ingress_port;
  int egress_port;
  ConcreteHeader ingress_packet;  // Input packet into the program/switch.
  ConcreteHeader egress_packet;   // Expected output packet.
  // Expected metadata field values at the end of execution.
  // E.g. if vrf is set to different values through out the execution of the
  // program on this packet, this will contain the last value set for the vrf.
  ConcreteMetadata metadata;
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
  SymbolicMetadata metadata;  // Metadata symbols at the end of execution.
  SymbolicTrace trace;
};

// The dataplane configuration of the switch.
// Used as input to our symbolic pipeline.
struct Dataplane {
  ir::P4Program program;
  // Maps the full name of a table to a list of its entries.
  ir::TableEntries entries;
};

// The overall state of our symbolic solver/interpreter.
// This is returned by our main analysis/interpration function, and is used
// to find concrete test packets and for debugging.
// This is internal to our solver code. External code that uses our solver
// is not expected to access any of these fields or modify them.
// Only one instance of this struct will be constructed per P4 program
// evaluation, which can be then used to solve for particular assertions
// many times.
struct SolverState {
  // The IR represnetation of the p4 program being analyzed.
  ir::P4Program program;
  // Maps the name of a table to a list of its entries.
  ir::TableEntries entries;
  // The symbolic context of our interpretation/analysis of the program,
  // including symbolic handles on packet headers and its trace.
  SymbolicContext context;
  // Context must remain in scope, otherwise when it gets cleaned, accessing
  // previously defined variables and constraints will result in segfaults!
  // This is the same pointer as the global Z3_CONTEXT.
  // This struct owns that pointer, when this struct is deleted
  // the pointer is also cleaned. The global pointer is set again
  // on calls to EvaluatP4Pipeline, which returns an instance of this struct
  // that owns that new pointer.
  std::unique_ptr<z3::context> z3_context;
  // Having the z3 solver defined here allows Z3 to remember interesting
  // deductions it made while solving for one particular assertion, and re-use
  // them during solving with future assertions.
  std::unique_ptr<z3::solver> solver;
  // clean up Z3 internal memory datastructures, Z3 can still be
  // used after this, as if Z3 has been freshly loaded.
  // Makes sense to use here, when SolverState is destructed, it means
  // no further analysis of the particular program is possible.
  // https://github.com/Z3Prover/z3/issues/157
  ~SolverState() {
    Z3_API Z3_reset_memory();
    // No need to delete Z3_CONTEXT explicitly.
    // Destructor of z3_context of type unique_ptr will handle it.
    // Set it to nullptr to mark it gone!
    Z3_CONTEXT = nullptr;
    // After this, solver will be automatically destructed, and then z3_context!
  }
};

// Instances of these structs are passed around and returned between our
// internal evaluation functions. An instance of this struct captures
// the symbolic state of the P4 program being evaluated at the current
// step in the interpration.
struct SymbolicPerPacketState {
  SymbolicHeader header;
  SymbolicMetadata metadata;
};

// An assertion is a user defined function that takes a symbolic context
// as input, and returns constraints on symbolic handles exposed by that
// context. For example:
// z3::expr portIsOne(const SymbolicContext &ctx) {
//   return ctx.ingress_port == 1;
// }
using Assertion = std::function<z3::expr(const SymbolicContext &)>;

// Symbolically evaluates/interprets the given program against the given
// entries for every table in that program, and the available physical ports
// on the switch.
pdpi::StatusOr<SolverState *> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports);

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by solver_state.
pdpi::StatusOr<ConcreteContext> Solve(SolverState *solver_state,
                                      const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(SolverState *solver_state, const Assertion &assertion);

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
