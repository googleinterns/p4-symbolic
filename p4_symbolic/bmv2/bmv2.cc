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

#include "p4_symbolic/bmv2/bmv2.h"

#include "google/protobuf/util/json_util.h"
#include "p4_symbolic/util/io.h"
#include "p4_symbolic/util/status.h"

namespace p4_symbolic {
namespace bmv2 {

// Parse the content of the given file using
// google::protobuf::util::JsonStringToMessage.
// If that call fails, its failure status is returned.
absl::Status parse_bmv2_json(std::string json_path, P4Program *output) {
  // Verify link and compile versions are the same.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // Read input json from file.
  std::string input;
  absl::Status read_status = p4_symbolic::util::ReadFile(json_path, &input);
  if (!read_status.ok()) {
    return read_status;
  }

  // Parsing JSON with protobuf.
  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = true;
  google::protobuf::util::Status parse_status =
      google::protobuf::util::JsonStringToMessage(input, output, options);

  if (!parse_status.ok()) {
    return p4_symbolic::util::protobuf_to_absl_status(parse_status);
  }

  return absl::OkStatus();
}

}  // namespace bmv2
}  // namespace p4_symbolic
