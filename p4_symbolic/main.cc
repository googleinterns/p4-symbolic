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

// TODO(babman): use abseil for command line argument parsing.
// Stub main file for debugging (for now).

#include <iostream>
#include <string>

#include "p4_symbolic/bmv2/bmv2.h"
#include "p4_symbolic/ir/pdpi_driver.h"

// The main test routine for parsing bmv2 json with protobuf.
// Parses bmv2 json that is fed in through stdin and dumps
// the resulting native protobuf and json data to files.
// Expects the paths of the protobuf output file and json
// output file to be passed as command line arguments respectively.
int main(int argc, char* argv[]) {
  // Verify link and compile versions are the same.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Parse pdpi.
  pdpi::StatusOr<pdpi::ir::IrP4Info> p4info_or_status =
      p4_symbolic::ir::ParseP4InfoFile(argv[1]);

  if (!p4info_or_status.ok()) {
    std::cerr << "Could not parse p4info: " << p4info_or_status.status()
              << std::endl;
    return 1;
  }

  // Parse bmv2 json.
  pdpi::StatusOr<p4_symbolic::bmv2::P4Program> bmv2_or_status =
      p4_symbolic::bmv2::ParseBmv2JsonFile(argv[2]);

  if (!bmv2_or_status.ok()) {
    std::cerr << "Could not parse bmv2 JSON: " << bmv2_or_status.status()
              << std::endl;
    return 1;
  }

  // Dump debugging output.
  std::cout << p4info_or_status.value().DebugString() << std::endl;
  std::cout << "============" << std::endl;
  std::cout << bmv2_or_status.value().DebugString() << std::endl;
  return 0;
}
