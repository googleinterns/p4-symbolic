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

// Helpful utilities for managing symbolic and concrete headers and values.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H_
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H_

#include <string>
#include <unordered_map>

#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

// Free (unconstrained) symbolic headers consisting of free symbolic variables
// for every field in every header instance defined in the P4 program.
gutil::StatusOr<std::unordered_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers);

// Returns an symbolic table match containing default values.
// The table match expression is false, the index is -1, and the value is
// undefined.
SymbolicTableMatch DefaultTableMatch();

// Extract a concrete context by evaluating every component's corresponding
// expression in the model.
gutil::StatusOr<ConcreteContext> ExtractFromModel(
    SymbolicContext context, z3::model model,
    const values::ValueFormatter &value_formatter);

// Merges two symbolic traces into a single trace. A field in the new trace
// has the value of the changed trace if the condition is true, and the value
// of the original one otherwise.
// Assertion: both traces must contain matches for the same set of table names.
gutil::StatusOr<SymbolicTrace> MergeTracesOnCondition(
    const z3::expr &condition, const SymbolicTrace &true_trace,
    const SymbolicTrace &false_trace);

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
gutil::StatusOr<z3::expr> Bmv2ValueZ3Expr(const pdpi::IrValue &value);

// Transforms a value read from a table entry to a z3::expr.
// On top of formatting ipv4, ipv6, hexstrings, and macs as bitvectors,
// this function also translates string values to unique and arbitrary
// bitvectors.
// The mapping of strings to bitvectors is stored and used to map the same
// string to the same consistent bitvector, and to also do a reverse-translation
// when extracting values for headers and fields from the z3 model.
gutil::StatusOr<z3::expr> P4RTValueZ3Expr(const std::string field_name,
                                          const pdpi::IrValue &value);

// Exposes a static mapping from string values to bitvector values.
// We do not need to include field names here because we assume the string
// values are unique.
std::unordered_map<std::string, uint64_t> &StringToBitVectorTranslationMap();

// Exposes a static mapping from field names and bitvector values to
// string values.
std::unordered_map<std::string, std::unordered_map<uint64_t, std::string>>
    &BitVectorToStringTranslationMap();

// Exposes a static mapping from field name to count of strings translated
// for that field.
std::unordered_map<std::string, uint64_t> &FieldNameToStringCountMap();

// Reverse translation of internal values from the p4/bmv2 value domain
// to the string domain of P4RT.
// If this is called on values belonging to fields without a
// @p4runtime_translation annotation, it is a no-op.
gutil::StatusOr<std::string> TranslateValueToString(
    const std::string field_name, const std::string &value);

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_UTIL_H_
