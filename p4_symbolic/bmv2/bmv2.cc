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
pdpi::StatusOr<P4Program> ParseBmv2Json(std::string json_path) {
  // Read input json from file.
  pdpi::StatusOr<std::string> read_status = util::ReadFile(json_path);
  RETURN_IF_ERROR(read_status.status());

  // Parsing JSON with protobuf.
  P4Program output;
  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = true;
  google::protobuf::util::Status parse_status =
      google::protobuf::util::JsonStringToMessage(read_status.value(), &output,
                                                  options);
  RETURN_IF_ERROR(util::ProtobufToAbslStatus(parse_status));

  return pdpi::StatusOr<P4Program>(output);
}

}  // namespace bmv2
}  // namespace p4_symbolic
