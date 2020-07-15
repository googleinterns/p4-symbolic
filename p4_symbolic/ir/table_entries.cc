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

#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "p4_symbolic/util/io.h"

namespace p4_symbolic {
namespace ir {
namespace {

struct TableEntryPair {
  // The alias of the table this entry belongs to.
  // This is translated to a fully qualified name during the IR transformation.
  std::string table_alias;
  // This is injected into the IR structure when the IR is produced.
  TableEntry entry_data;
};

gutil::StatusOr<TableEntryPair> ParseLine(const std::string &line) {
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

    int val = std::atoi(tokens[i].c_str());
    if (found_delimiter) {
      output.add_action_parameters(val);
    } else {
      output.add_match_values(val);
    }
  }

  return TableEntryPair{tokens[1], output};
}

}  // namespace

gutil::StatusOr<TableEntries> ParseAndFillEntries(
    const pdpi::IrP4Info &pdpi, const std::string &entries_path) {
  ASSIGN_OR_RETURN(std::string file_content, util::ReadFile(entries_path));

  // Skip empty lines or ones that only contain whitespace.
  std::vector<std::string> lines =
      absl::StrSplit(file_content, '\n', absl::SkipWhitespace());

  TableEntries output;
  // Parse table entries one line at a time.
  for (const std::string &line : lines) {
    ASSIGN_OR_RETURN(TableEntryPair pair, ParseLine(line));
    // Table and action aliases parsed from table entris files
    // will be replaced with their respective full name.
    TableEntry entry = pair.entry_data;
    const std::string &table_alias = pair.table_alias;
    const std::string &action_alias = entry.action();

    // Make sure both table and action referred to by entry exist.
    RET_CHECK(pdpi.tables_by_name().count(table_alias) == 1);
    RET_CHECK(pdpi.actions_by_name().count(action_alias) == 1);

    const std::string &table_name =
        pdpi.tables_by_name().at(table_alias).preamble().name();
    const std::string &action_name =
        pdpi.actions_by_name().at(action_alias).preamble().name();

    entry.set_action(action_name);
    output[table_name].push_back(entry);
  }

  return output;
}

}  // namespace ir
}  // namespace p4_symbolic
