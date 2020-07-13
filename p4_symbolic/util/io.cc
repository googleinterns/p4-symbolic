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

#include "p4_symbolic/util/io.h"

#include <cerrno>
#include <fstream>
#include <streambuf>
#include <string>

#include "absl/strings/str_format.h"
#include "p4_pdpi/utils/status_utils.h"

namespace p4_symbolic {
namespace util {

pdpi::StatusOr<std::string> ReadFile(const std::string &path) {
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
  return std::string(std::istreambuf_iterator<char>(f),
                     std::istreambuf_iterator<char>());
}

}  // namespace util
}  // namespace p4_symbolic
