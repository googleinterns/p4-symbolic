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

// This file is responsible for parsing values from the bmv2 json and table
// entries.
// It is also responsible for translating any string values to corresponding
// bitvectors and back, for fields that have the @p4runtime_translation
// annotation.

#ifndef P4_SYMBOLIC_SYMBOLIC_VALUES_H_
#define P4_SYMBOLIC_SYMBOLIC_VALUES_H_

#include <string>
#include <unordered_map>

#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace values {

// Transforms a hex string literal from bmv2 json to a pdpi::IrValue
gutil::StatusOr<pdpi::IrValue> ParseIrValue(std::string value);

// Transforms a value read from bmv2 (e.g. hardcoded in the program)
// to a z3::expr.
// Essentially, this is just a formatting function that can format ipv4, ipv6
// hexstrings, and macs as bitvectors in z3's format.
// This function does not perform any string translation, and instead assumes
// the values are already in the actual domain of values in the p4 program,
// because p4 and bmv2 both do not support string translation, it is only used
// as a logical translation at the boundry between P4RT and bmv2.
gutil::StatusOr<z3::expr> FormatBmv2Value(const pdpi::IrValue &value);

// This class is responsible for formatting various values into consistent
// format acceptable by z3.
// The class transforms pdpi::IrValue instances to z3::expr, it also handles
// translation (and reverse translation) of P4RT string values that are meant
// to be translated to bitvectors, because of @p4runtime_translation
// annotations.
class ValueFormatter {
 public:
  // Transforms a value read from a table entry to a z3::expr.
  // On top of formatting ipv4, ipv6, hexstrings, and macs as bitvectors,
  // this function also translates string values to unique and arbitrary
  // bitvectors.
  // The mapping of strings to bitvectors is stored and used to map the same
  // string to the same consistent bitvector, and to also do a
  // reverse-translation when extracting values for headers and fields from the
  // z3 model.
  gutil::StatusOr<z3::expr> FormatP4RTValue(const std::string field_name,
                                            const pdpi::IrValue &value);

  // Reverse translation of internal values from the p4/bmv2 value domain
  // to the string domain of P4RT.
  // If this is called on values belonging to fields without a
  // @p4runtime_translation annotation, it is a no-op.
  gutil::StatusOr<std::string> TranslateValueToString(
      const std::string field_name, const std::string &value) const;

 private:
  // A mapping from string values to bitvector values.
  // We do not need to include field names here because we assume the string
  // values are unique.
  std::unordered_map<std::string, z3::expr> string_to_bitvector_map_;

  // A mapping from field names and bitvector values to string values.
  std::unordered_map<std::string, std::unordered_map<std::string, std::string>>
      field_name_to_string_map_;

  // A mapping from field name to count of strings translated for that field.
  // This is used to come up with new unique (per field) bitvector values
  // for newly encountered strings.
  std::unordered_map<std::string, uint64_t> field_name_to_string_count_map_;
};

}  // namespace values
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_VALUES_H_
