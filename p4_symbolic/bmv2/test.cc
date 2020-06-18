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

// This is a test file for our protobuf specifications of bmv2 json.
// It reads an input bmv2 json string (usually the output of p4c) via stdin,
// it parses the string using protobuf, and then dumps the parsed protobuf
// objects using protobuf text format and json.
// The dumps are written to output files whose paths are provided as command
// line arguments.

#include <fstream>
#include <iostream>
#include <string>

#include "google/protobuf/text_format.h"
#include "google/protobuf/util/json_util.h"
#include "p4_symbolic/bmv2/bmv2.h"

// Write a string to a file.
void WriteFile(char path[], const std::string& content) {
  std::ofstream out;
  out.open(path);
  out << content;
  out.close();
}

// The main test routine for parsing bmv2 json with protobuf.
// Parses bmv2 json file and dumps the resulting bmv2 protobuf
// and json data to files.
// Expects the paths of the input json file and the protobuf and json output
// files to be passed as command line arguments in order.
int main(int argc, char* argv[]) {
  // Verify link and compile versions are the same.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Validate command line arguments.
  if (argc != 4) {
    std::cout << "Usage: ./main <input JSON file> <protobuf output file> <json "
                 "output file>."
              << std::endl;
    return 0;
  }

  // Parse JSON using bmv2.cc.
  std::string input(argv[1]);
  pdpi::StatusOr<p4_symbolic::bmv2::P4Program> status =
      p4_symbolic::bmv2::ParseBmv2Json(input);
  if (!status.ok()) {
    std::cerr << "Error reading input file: " << status.status() << std::endl;
    return 1;
  }

  // Dumping protobuf.
  std::string protobuf_output_str;
  google::protobuf::TextFormat::PrintToString(status.value(),
                                              &protobuf_output_str);
  WriteFile(argv[2], protobuf_output_str);

  // Dumping JSON.
  google::protobuf::util::JsonPrintOptions dumping_options;
  dumping_options.add_whitespace = true;
  dumping_options.always_print_primitive_fields = true;
  dumping_options.preserve_proto_field_names = true;

  std::string json_output_str;
  google::protobuf::util::MessageToJsonString(status.value(), &json_output_str,
                                              dumping_options);
  WriteFile(argv[3], json_output_str);

  // Clean up.
  google::protobuf::ShutdownProtobufLibrary();

  // Exit.
  return 0;
}
