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

#include "p4_symbolic/util/io.h"

#include <cerrno>
#include <fstream>
#include <streambuf>

#include "absl/strings/str_format.h"
#include "p4_pdpi/utils/status_utils.h"

namespace p4_symbolic {
namespace util {

pdpi::StatusOr<std::string> ReadFile(std::string path) {
  std::ifstream f;
  f.open(path.c_str());
  if (f.fail()) {
    std::string err;
    switch (errno) {
      case EACCES:
      case ENOENT:
        err = absl::StrFormat("%s: %s", strerror(errno), path);
        return pdpi::StatusOr<std::string>(
            absl::Status(absl::StatusCode::kNotFound, err));
      default:
        err = absl::StrFormat("Cannot read file %s, errno = %d", path, errno);
        return pdpi::StatusOr<std::string>(
            absl::Status(absl::StatusCode::kUnknown, err));
    }
  }

  f >> std::noskipws;  // Read whitespaces.
  std::string output(std::istreambuf_iterator<char>(f),
                     (std::istreambuf_iterator<char>()));
  return pdpi::StatusOr<std::string>(output);
}

}  // namespace util
}  // namespace p4_symbolic
