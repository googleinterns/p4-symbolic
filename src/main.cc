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

#include <iostream>
#include <fstream>
#include <string>

#include "google/protobuf/util/json_util.h"
#include "google/protobuf/text_format.h"

#include "src/protobuf/bmv2/program.pb.h"

// Read all of stdin up to EOF.
inline std::string ReadStdin() {
  std::istreambuf_iterator<char> cin_iterator{std::cin};
  std::istreambuf_iterator<char> end;
  return std::string(cin_iterator, end);
}

// Write a string to a file.
void WriteFile(char path[], const std::string& content) {
  std::ofstream out;
  out.open(path);
  out << content;
  out.close();
}

// The main test routine for parsing bmv2 json with protobuf.
// Parses bmv2 json that is fed in through stdin and dumps
// the resulting native protobuf and json data to files.
// Expects the paths of the protobuf output file and json
// output file to be passed as command line arguments respectively.
int main(int argc, char* argv[]) {
  // Verify link and compile versions are the same.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Validate command line arguments.
  if (argc != 3) {
    std::cout << "Usage: ./main <protobuf output file> <json output file>."
        << std::endl;
    return 0;
  }

  // Read input json from stdin.
  std::string input = ReadStdin();

  // Parsing JSON with protobuf.
  P4Program p4_buf;
  google::protobuf::util::JsonParseOptions parsing_options;
  parsing_options.ignore_unknown_fields = true;
  google::protobuf::util::JsonStringToMessage(input, &p4_buf, parsing_options);

  // Dumping protobuf.
  std::string protobuf_output_str;
  google::protobuf::TextFormat::PrintToString(p4_buf, &protobuf_output_str);
  WriteFile(argv[1], protobuf_output_str);

  // Dumping JSON.
  google::protobuf::util::JsonPrintOptions dumping_options;
  dumping_options.add_whitespace = true;
  dumping_options.always_print_primitive_fields = true;
  dumping_options.preserve_proto_field_names = true;

  std::string json_output_str;
  google::protobuf::util::MessageToJsonString(p4_buf,
                                              &json_output_str,
                                              dumping_options);
  WriteFile(argv[2], json_output_str);

  // Clean up.
  google::protobuf::ShutdownProtobufLibrary();

  // Exit.
  return 0;
}
