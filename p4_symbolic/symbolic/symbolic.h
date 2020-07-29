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
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/symbolic/typed.h"
#include "z3++.h"  // TODO(babman): added as a system dependency for now.

namespace p4_symbolic {
namespace symbolic {

// Global z3::context used for creating symbolic expressions during symbolic
// evaluation.
z3::context &Z3Context();

// Maps the name of a header field in the p4 program to its concrete value.
using ConcreteHeaders = std::unordered_map<std::string, std::string>;

// The symbolic counterpart of ConcreteHeader.
// Maps the name of a header field in the p4 program to its symbolic value.
// This can be used to constrain p4 program fields.
// This is automatically constructred from the header type definitions
// the p4 program has.
// Assume the p4 program has a header instance named "standard_metadata" of type
// "standard_metadata_t", which has field "ingress_port" of type "bit<9>" in it.
// Then, we will have:
//     SymbolicMetadata["standard_metadata.ingress_port"] =
//         TypedExpr<symbolic bit vector of size 9>
using SymbolicHeaders = std::unordered_map<std::string, TypedExpr>;

// Expresses a concrete match for a corresponding concrete packet with a
// table in the program.
struct ConcreteTableMatch {
  bool matched;  // false if no entry in this table was matched, true otherwise.
  // if matched is false, these two fields are set to -1.
  int entry_index;
  std::string value;
};

// Exposes a symbolic handle for a match between the symbolic packet and
// a symbolic table.
// This allows encoding of constraints on which (if any) entries are matched,
// and the value of the match.
// e.g. for some table "<table_name>":
// 1. (<symbolic_table_match>.entry_index == i) iff
//    <entries>[<table_name>][i] was matched/hit.
struct SymbolicTableMatch {
  TypedExpr matched;
  TypedExpr entry_index;
  TypedExpr value;
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
  // Full table name to its symbolic match.
  std::unordered_map<std::string, SymbolicTableMatch> matched_entries;
  TypedExpr dropped;
};

// Specifies the concrete data inside a packet.
// This is a friendly helper struct, all information in this struct
// is extracted from ConcreteHeader.
struct ConcretePacket {
  std::string eth_src;
  std::string eth_dst;
  std::string eth_type;

  std::string outer_ipv4_src;
  std::string outer_ipv4_dst;
  std::string outer_ipv6_dst_upper;
  std::string outer_ipv6_dst_lower;
  std::string outer_protocol;
  std::string outer_dscp;
  std::string outer_ttl;

  std::string inner_ipv4_dst;
  std::string inner_ipv6_dst_upper;
  std::string inner_ipv6_dst_lower;
  std::string inner_protocol;
  std::string inner_dscp;
  std::string inner_ttl;

  std::string icmp_type;
  std::string vid;
};

// A helper struct containing symbolic expressions for every field in a packet.
// All expressions in this struct are extracted from SymbolicHeader.
// We explicitly give these fields name in this struct to simplify how the
// client code can impose constraints on them in assertions.
struct SymbolicPacket {
  TypedExpr eth_src;   // 48 bit.
  TypedExpr eth_dst;   // 48 bit.
  TypedExpr eth_type;  // 16 bit.

  TypedExpr outer_ipv4_src;        // 32 bit, valid if eth_type = 0x0800
  TypedExpr outer_ipv4_dst;        // 32 bit, valid if eth_type = 0x0800
  TypedExpr outer_ipv6_dst_upper;  // 64 bit, valid if eth_type = 0x86dd
  TypedExpr outer_ipv6_dst_lower;  // 64 bit, valid if eth_type = 0x86dd
  TypedExpr outer_protocol;        // 8 bit, valid if eth_type is ip
  TypedExpr outer_dscp;            // 6 bit, valid if eth_type is ip
  TypedExpr outer_ttl;             // 8 bit, valid if eth_type is ip

  TypedExpr inner_ipv4_dst;        // 32 bit, valid if outer_protocol = 4
  TypedExpr inner_ipv6_dst_upper;  // 64 bit, valid if outer_protocol = 4
  TypedExpr inner_ipv6_dst_lower;  // 64 bit, valid if outer_protocol = 41
  TypedExpr inner_protocol;        // 8 bit, valid if outer_protocol = 4/41
  TypedExpr inner_dscp;            // 6 bit, valid if outer_protocol = 4/41
  TypedExpr inner_ttl;             // 8 bit, valid if outer_protocol = 4/41

  TypedExpr icmp_type;  // 8 bit, valid if eth_type is ip
  TypedExpr vid;        // 12 bit, valid if eth_type = 0x6007
};

// The result of solving with some assertion.
// This contains an input test packet with its predicted flow in the program,
// and the predicted output.
struct ConcreteContext {
  std::string ingress_port;
  std::string egress_port;
  ConcretePacket ingress_packet;  // Input packet into the program/switch.
  ConcretePacket egress_packet;   // Expected output packet.
  // Expected header field values at the end of execution.
  // E.g. if vrf is set to different values through out the execution of the
  // program on this packet, this will contain the last value set for the vrf.
  ConcreteHeaders headers;
  ConcreteTrace trace;  // Expected trace in the program.
};

// The symbolic context within our analysis.
// Exposes symbolic handles for the fields of the input packet,
// and its trace in the program.
// Assertions are defined on a symbolic context.
struct SymbolicContext {
  TypedExpr ingress_port;
  TypedExpr egress_port;
  SymbolicPacket ingress_packet;
  SymbolicPacket egress_packet;
  SymbolicHeaders headers;  // Header symbols at the end of execution.
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
  // Having the z3 solver defined here allows Z3 to remember interesting
  // deductions it made while solving for one particular assertion, and re-use
  // them during solving with future assertions.
  std::unique_ptr<z3::solver> solver;
  // Need this constructor to be defined explicity to be able to use make_unique
  // on this struct.
  SolverState(ir::P4Program program, ir::TableEntries entries,
              SymbolicContext context, std::unique_ptr<z3::solver> &&solver)
      : program(program),
        entries(entries),
        context(context),
        solver(std::move(solver)) {}
};

// An assertion is a user defined function that takes a symbolic context
// as input, and returns constraints on symbolic handles exposed by that
// context. For example:
// z3::expr portIsOne(const SymbolicContext &ctx) {
//   return ctx.ingress_port.expr() == 1;
// }
using Assertion = std::function<z3::expr(const SymbolicContext &)>;

// Symbolically evaluates/interprets the given program against the given
// entries for every table in that program, and the available physical ports
// on the switch.
gutil::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports);

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by solver_state.
gutil::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion);

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
