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

#include "p4_symbolic/ir/table_entries.h"

#include <iostream>
#include <regex>
#include <string>

#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "p4_symbolic/util/io.h"

namespace p4_symbolic {
namespace ir {

// TODO(babman): unclear if we need this right now.
//               Ideally, we want to represent everything as bitvectors,
//               However, Z3 API may provide a better way to encode/transform
//               to hex.
pdpi::StatusOr<std::string> FormatBitStringAsHex(std::string str) {
  // detect the format: either a number, an IP, an IP range or a mac address.
  std::regex number("^([0-9]+)$");
  std::regex ip("^([0-9]+)\\.([0-9]+)\\.([0-9]+)\\.([0-9]+)$");
  std::regex ip_range("^([0-9]+)\\.([0-9]+)\\.([0-9]+)\\.([0-9]+)/([0-9]+)$");
  std::regex mac("^(?:([0-9A-Fa-f]{2}):){5}([0-9A-Fa-f]{2})$");

  std::smatch sm;
  if (std::regex_match(str, sm, number)) {
  } else if (std::regex_match(str, sm, ip)) {
  } else if (std::regex_match(str, sm, ip_range)) {
  } else if (std::regex_match(str, sm, mac)) {
  } else {
    return absl::Status(absl::StatusCode::kInvalidArgument,
                        absl::StrFormat("Malformed table entry value %s", str));
  }

  return str;
}

pdpi::StatusOr<std::pair<std::string, TableEntry>> ParseLine(
    const std::string &line) {
  std::vector<std::string> tokens =
      absl::StrSplit(line, ' ', absl::SkipWhitespace());
  if (tokens.size() < 3) {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Malformed table entry, found %s", line));
  }
  if (tokens[0] != "table_add") {
    return absl::Status(
        absl::StatusCode::kInvalidArgument,
        absl::StrFormat("Malformed table entry command %s, found %s", tokens[0],
                        line));
  }

  // Parse table entries.
  TableEntry output;
  output.set_action(tokens[2]);
  bool found_delimiter = false;  // true when "=>" is found.
  for (size_t i = 3; i < tokens.size(); i++) {
    if (tokens[i] == "=>") {
      found_delimiter = true;
      continue;
    }

    ASSIGN_OR_RETURN(std::string hexstr, FormatBitStringAsHex(tokens[i]));
    if (found_delimiter) {
      output.add_action_parameters(hexstr);
    } else {
      output.add_match_values(hexstr);
    }
  }

  return std::make_pair(tokens[1], output);
}

pdpi::StatusOr<TableEntries> ParseAndFillEntries(const char *entries_path) {
  ASSIGN_OR_RETURN(std::string file_content, util::ReadFile(entries_path));

  // Skip empty lines or ones that only contain whitespace.
  std::vector<std::string> lines =
      absl::StrSplit(file_content, '\n', absl::SkipWhitespace());

  std::vector<std::pair<std::string, TableEntry>> output;
  for (const std::string &line : lines) {
    ASSIGN_OR_RETURN(auto entry, ParseLine(line));
    output.push_back(entry);
  }

  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
