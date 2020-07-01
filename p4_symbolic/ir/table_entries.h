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

// This file parses table entries attached to a p4 program, and fills them
// into the IR of that program.

#ifndef P4_SYMBOLIC_IR_TABLE_ENTRIES_H_
#define P4_SYMBOLIC_IR_TABLE_ENTRIES_H_

#include <string>
#include <utility>
#include <vector>

#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace ir {

struct TableEntryPair {
  // The alias of the table this entry belongs to.
  // This is translated to a fully qualified name during the IR transformation.
  std::string table_alias;
  // This is injected into the IR structure when the IR is produced.
  TableEntry entry_data;
};

using TableEntries = std::vector<TableEntryPair>;

// Parses entries read from entries_path, and fills them in given ir in place.
pdpi::StatusOr<TableEntries> ParseAndFillEntries(
    const std::string &entries_path);

}  // namespace ir
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_IR_TABLE_ENTRIES_H_
