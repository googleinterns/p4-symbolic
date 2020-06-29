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

// Main file for finding P4 test packets symbolically.
// Expects input bmv2 json, p4info, and table entries files as command
// line flags.
// Produces test packets that hit every row in the P4 program tables.

#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/parser.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/util/io.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");
ABSL_FLAG(std::string, debug, "", "Dump the SMT program for debugging");

// The main test routine for parsing bmv2 json with protobuf.
// Parses bmv2 json that is fed in through stdin and dumps
// the resulting native protobuf and json data to files.
// Expects the paths of the protobuf output file and json
// output file to be passed as command line arguments respectively.
int main(int argc, char *argv[]) {
  // Verify link and compile versions are the same.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Command line arugments and help message.
  absl::SetProgramUsageMessage(
      absl::StrFormat("usage: %s %s", argv[0],
                      "--bmv2=path/to/bmv2.json --p4info=path/to/p4info.pb.txt "
                      "[--entries=path/to/table_entries.txt]"));
  absl::ParseCommandLine(argc, argv);

  const std::string &p4info_path = absl::GetFlag(FLAGS_p4info);
  const std::string &bmv2_path = absl::GetFlag(FLAGS_bmv2);
  const std::string &entries_path = absl::GetFlag(FLAGS_entries);
  const std::string &debug_path = absl::GetFlag(FLAGS_debug);
  if (p4info_path.empty()) {
    std::cerr << "Missing argument: --p4info=<file>" << std::endl;
    return 1;
  }
  if (bmv2_path.empty()) {
    std::cerr << "Missing argument: --bmv2=<file>" << std::endl;
    return 1;
  }

  // Transform to IR.
  pdpi::StatusOr<p4_symbolic::symbolic::Dataplane> parser_status =
      p4_symbolic::ParseToIr(bmv2_path, p4info_path, entries_path);
  if (!parser_status.ok()) {
    std::cerr << "Could not transform to IR: " << parser_status.status()
              << std::endl;
  }

  // Analyze program symbolically.
  p4_symbolic::symbolic::Dataplane dataplane = parser_status.value();
  pdpi::StatusOr<std::unique_ptr<p4_symbolic::symbolic::SolverState>>
      solver_status = p4_symbolic::symbolic::EvaluateP4Pipeline(
          dataplane, std::vector<int>{0, 1});
  if (!solver_status.ok()) {
    std::cerr << "Could not analyze program symbolically: "
              << solver_status.status() << std::endl;
    return 1;
  }

  // Find a packet matching every entry of every table.
  std::string debug_smt_formula = "";
  const std::unique_ptr<p4_symbolic::symbolic::SolverState> &solver_state =
      solver_status.value();
  for (const auto &[name, table] : dataplane.program.tables()) {
    for (int i = 0; i < dataplane.entries[name].size(); i++) {
      std::cout << "Finding packet for table " << name << " and row " << i
                << std::endl;

      p4_symbolic::symbolic::Assertion table_entry_assertion =
          [name,
           i](const p4_symbolic::symbolic::SymbolicContext &symbolic_context) {
            const p4_symbolic::symbolic::SymbolicTableMatch &match =
                symbolic_context.trace.matched_entries.at(name);
            return (!symbolic_context.trace.dropped && match.matched &&
                    match.entry_index == i);
          };

      debug_smt_formula = absl::StrCat(
          debug_smt_formula,
          p4_symbolic::symbolic::DebugSMT(solver_state, table_entry_assertion),
          "\n");

      pdpi::StatusOr<std::optional<p4_symbolic::symbolic::ConcreteContext>>
          packet_status =
              p4_symbolic::symbolic::Solve(solver_state, table_entry_assertion);
      if (!packet_status.ok()) {
        std::cout << "\t" << packet_status.status() << std::endl << std::endl;
        continue;
      }
      std::optional<p4_symbolic::symbolic::ConcreteContext> packet_option =
          packet_status.value();
      if (packet_option) {
        std::cout << "\tstandard_metadata.ingress_port = "
                  << packet_option.value().ingress_port << std::endl;
        std::cout << "\tstandard_metadata.egress_spec = "
                  << packet_option.value().egress_port << std::endl;
      } else {
        std::cout << "Cannot find solution!" << std::endl;
      }
      std::cout << std::endl;
    }
  }

  // Debugging.
  if (!debug_path.empty()) {
    absl::Status debug_status =
        p4_symbolic::util::WriteFile(debug_smt_formula, debug_path);
    if (!debug_status.ok()) {
      std::cerr << "Could not dump debugging SMT program: " << debug_status
                << std::endl;
      return 1;
    }
  }

  // Clean up
  google::protobuf::ShutdownProtobufLibrary();

  return 0;
}
