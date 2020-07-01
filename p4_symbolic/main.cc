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

// Stub main file for debugging (for now).

#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/strings/str_format.h"
#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/pdpi_driver.h"
#include "p4_symbolic/ir/table_entries.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");

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
  if (p4info_path.empty()) {
    std::cerr << "Missing argument: --p4info=<file>" << std::endl;
    return 1;
  }
  if (bmv2_path.empty()) {
    std::cerr << "Missing argument: --bmv2=<file>" << std::endl;
    return 1;
  }

  // Parse pdpi.
  pdpi::StatusOr<pdpi::ir::IrP4Info> p4info_or_status =
      p4_symbolic::ir::ParseP4InfoFile(p4info_path);

  if (!p4info_or_status.ok()) {
    std::cerr << "Could not parse p4info: " << p4info_or_status.status()
              << std::endl;
    return 1;
  }

  // Parse bmv2 json.
  pdpi::StatusOr<p4_symbolic::bmv2::P4Program> bmv2_or_status =
      p4_symbolic::bmv2::ParseBmv2JsonFile(bmv2_path);

  if (!bmv2_or_status.ok()) {
    std::cerr << "Could not parse bmv2 JSON: " << bmv2_or_status.status()
              << std::endl;
    return 1;
  }

  // Parse table entries.
  p4_symbolic::ir::TableEntries table_entries;
  if (!entries_path.empty()) {
    pdpi::StatusOr<p4_symbolic::ir::TableEntries> table_entries_or_status =
        p4_symbolic::ir::ParseAndFillEntries(entries_path);

    if (!table_entries_or_status.ok()) {
      std::cerr << "Could not parse table entries: "
                << table_entries_or_status.status() << std::endl;
      return 1;
    }
    table_entries = table_entries_or_status.value();
  }

  // Transform to IR and print.
  pdpi::StatusOr<p4_symbolic::ir::P4Program> ir_status =
      p4_symbolic::ir::Bmv2AndP4infoToIr(
          bmv2_or_status.value(), p4info_or_status.value(), table_entries);
  if (!ir_status.ok()) {
    std::cerr << "Could not transform to IR: " << ir_status.status()
              << std::endl;
    return 1;
  }

  std::cout << ir_status.value().DebugString() << std::endl;

  // Clean up
  google::protobuf::ShutdownProtobufLibrary();

  return 0;
}
