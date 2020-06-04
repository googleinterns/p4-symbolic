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

#include <iostream>
#include <string>

#include "google/protobuf/util/json_util.h"

#include "src/protobuf/bmv2/program.pb.h"

void ReadStdin(std::string* str) {
  std::istreambuf_iterator<char> cin_iterator{std::cin};
  std::istreambuf_iterator<char> end;
  *str = std::string(cin_iterator, end);
}

int main() {
  // verify link and compile versions are the same
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Read input json from stdin
  std::string* input = new std::string();
  ReadStdin(input);

  // parsing JSON
  P4Program p4buf;
  google::protobuf::util::JsonParseOptions parsing_options;
  parsing_options.ignore_unknown_fields = true;
  google::protobuf::util::JsonStringToMessage(*input, &p4buf, parsing_options);

  // printing JSON
  google::protobuf::util::JsonPrintOptions dumping_options;
  dumping_options.add_whitespace = true;
  dumping_options.always_print_primitive_fields = true;
  dumping_options.preserve_proto_field_names = true;

  std::string out;
  google::protobuf::util::MessageToJsonString(p4buf, &out, dumping_options);
  std::cout << out << std::endl;

  return 0;
}
