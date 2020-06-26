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

// Test file for producing IR representations of P4 Programs.

#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/flags/usage.h"
#include "absl/strings/str_format.h"
#include "p4_symbolic/parser.h"

ABSL_FLAG(std::string, p4info, "",
          "The path to the p4info protobuf file (required)");
ABSL_FLAG(std::string, bmv2, "", "The path to the bmv2 json file (required)");
ABSL_FLAG(std::string, entries, "",
          "The path to the table entries txt file (optional), leave this empty "
          "if the input p4 program contains no (explicit) tables for which "
          "entries are needed.");

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

  // Transform to IR and print.
  pdpi::StatusOr<p4_symbolic::symbolic::Dataplane> ir_status =
      p4_symbolic::ParseToIr(bmv2_path, p4info_path, entries_path);
  if (!ir_status.ok()) {
    std::cerr << "Could not transform to IR: " << ir_status.status()
              << std::endl;
    return 1;
  }

  // Dump string representation to stdout.
  p4_symbolic::symbolic::Dataplane dataplane = ir_status.value();
  std::cout << dataplane.program.DebugString() << std::endl;
  for (const auto &[name, entries] : dataplane.entries) {
    std::cout << "=====" << name << " Entries=====" << std::endl;
    for (const p4_symbolic::ir::TableEntry &entry : entries) {
      std::cout << entry.DebugString() << std::endl;
    }
  }

  // Clean up
  google::protobuf::ShutdownProtobufLibrary();

  return 0;
}
