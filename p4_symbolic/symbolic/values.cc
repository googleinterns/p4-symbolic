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

#include "p4_symbolic/symbolic/values.h"

#include <cstdint>
#include <locale>
#include <sstream>
#include <vector>

#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/strip.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {
namespace symbolic {
namespace values {

gutil::StatusOr<pdpi::IrValue> ParseIrValue(std::string value) {
  // Format according to type.
  if (absl::StartsWith(value, "0x")) {
    return pdpi::FormattedStringToIrValue(value, pdpi::Format::HEX_STRING);
  } else {
    // Some unsupported format!
    return absl::InvalidArgumentError(
        absl::StrCat("Literal value \"", value, "\" has unknown format!"));
  }
}

gutil::StatusOr<z3::expr> Bmv2ValueZ3Expr(const pdpi::IrValue &value) {
  switch (value.format_case()) {
    case pdpi::IrValue::kHexStr: {
      const std::string &hexstr = value.hex_str();

      uint64_t decimal;
      std::stringstream converter;
      converter << std::hex << hexstr;
      if (converter >> decimal) {
        unsigned int bitsize = 0;
        uint64_t pow = 1;
        while (bitsize <= 64 && pow <= decimal) {
          pow = pow * 2;
          bitsize++;
        }
        bitsize = (bitsize > 1 ? bitsize : 1);  // At least 1 bit.
        return Z3Context().bv_val(std::to_string(decimal).c_str(), bitsize);
      }

      return absl::InvalidArgumentError(absl::StrCat(
          "Cannot process hex string \"", hexstr, "\", the value is too big!"));
    }

    case pdpi::IrValue::kIpv4: {
      uint32_t ip = 0;
      std::vector<std::string> ipv4 = absl::StrSplit(value.ipv4(), ".");
      for (size_t i = 0; i < ipv4.size(); i++) {
        uint32_t shifted_component = static_cast<uint32_t>(std::stoull(ipv4[i]))
                                     << ((ipv4.size() - i - 1) * 8);
        ip += shifted_component;
      }
      return Z3Context().bv_val(std::to_string(ip).c_str(), 32);
    }

    case pdpi::IrValue::kMac: {
      uint64_t mac = 0;  // Mac is 6 bytes, we can fit them in 8 bytes.
      std::vector<std::string> split = absl::StrSplit(value.mac(), ":");
      for (size_t i = 0; i < split.size(); i++) {
        uint64_t decimal;  // Initially only 8 bits, but will be shifted.
        std::stringstream converter;
        converter << std::hex << split[i];
        if (converter >> decimal) {
          mac += decimal << ((split.size() - i - 1) * 8);
        } else {
          return absl::InvalidArgumentError(
              absl::StrCat("Cannot process mac value \"", value.mac(), "\"!"));
        }
      }
      return Z3Context().bv_val(std::to_string(mac).c_str(), 48);
    }

    case pdpi::IrValue::kIpv6: {
      uint64_t ipv6 = 0;  // Ipv6 is 128 bits, do it in two 64 bits steps.
      std::vector<std::string> split = absl::StrSplit(value.ipv6(), ":");

      // Transform the most significant 64 bits.
      for (size_t i = 0; i < split.size() / 2; i++) {
        uint64_t decimal;  // Initially only 16 bits, but will be shifted.
        std::stringstream converter;
        converter << std::hex << split[i];
        if (converter >> decimal) {
          ipv6 += decimal << ((split.size() / 2 - i - 1) * 16);
        } else {
          return absl::InvalidArgumentError(absl::StrCat(
              "Cannot process ipv6 value \"", value.ipv6(), "\"!"));
        }
      }
      z3::expr hi = Z3Context().bv_val(std::to_string(ipv6).c_str(), 128);

      // Transform the least significant 64 bits.
      ipv6 = 0;
      for (size_t i = split.size() / 2; i < split.size(); i++) {
        uint64_t decimal;
        std::stringstream converter;
        converter << std::hex << split[i];
        if (converter >> decimal) {
          ipv6 += decimal << ((split.size() - i - 1) * 16);
        } else {
          return absl::InvalidArgumentError(absl::StrCat(
              "Cannot process ipv6 value \"", value.ipv6(), "\"!"));
        }
      }
      z3::expr lo = Z3Context().bv_val(std::to_string(ipv6).c_str(), 128);

      // Add them together.
      z3::expr shift = Z3Context().bv_val("18446744073709551616", 128);  // 2^64
      ASSIGN_OR_RETURN(hi, operators::Times(hi, shift));  // shift << 64.
      return operators::Plus(hi, lo);
    }

    default:
      return absl::UnimplementedError(
          absl::StrCat("Found unsupported value type ", value.DebugString()));
  }
}

gutil::StatusOr<z3::expr> P4RTValueZ3Expr(const std::string field_name,
                                          const pdpi::IrValue &value) {
  switch (value.format_case()) {
    case pdpi::IrValue::kStr: {
      // Must translate the string into a bitvector.
      const std::string &string_value = value.str();
      auto &string_to_bitvector = StringToBitVectorTranslationMap();
      if (string_to_bitvector.count(string_value) == 1) {
        // This string was encountered previously and was already translated.
        z3::expr z3_value = string_to_bitvector.at(string_value);
        // Insert the previously translated value into the reverse mapping,
        // this is useful in case the same string value was previously
        // translated for a different field, this way that value gets tied
        // to this field as well.
        // If the value was previously translated for the same field, this
        // is a no-op.
        auto &bitvector_to_string = BitVectorToStringTranslationMap();
        if (bitvector_to_string.count(field_name) != 1) {
          bitvector_to_string.insert({field_name, {}});
        }
        bitvector_to_string.at(field_name)
            .insert({z3_value.to_string(), string_value});
        return z3_value;
      } else {
        // First time encountering this value. Come up with some bitvector
        // value for it unique relative to this field.
        auto &count_map = FieldNameToStringCountMap();
        if (count_map.count(field_name) != 1) {
          count_map.insert({field_name, 0});
        }
        uint64_t int_value = count_map.at(field_name)++;

        // Find the bitsize of int_value.
        // The bitvector will be created with that initial bitsize, if the
        // context of this value expected a larger bitsize, the value will be
        // padded at the context.
        // If the context expects a smaller bitsize, the context will return an
        // error, since that means the number of unique strings used exceed the
        // total size of the actual domain as defined in the p4 program.
        unsigned int bitsize = 0;
        uint64_t pow = 1;
        while (bitsize <= 64 && pow <= int_value) {
          pow = pow * 2;
          bitsize++;
        }
        bitsize = (bitsize > 1 ? bitsize : 1);  // At least 1 bit.
        z3::expr z3_value = Z3Context().bv_val(int_value, bitsize);

        // Store this z3::expr and its corresponding string value in the mapping
        // and reverse mapping for future lookups.
        string_to_bitvector.insert({string_value, z3_value});
        auto &bitvector_to_string = BitVectorToStringTranslationMap();
        if (bitvector_to_string.count(field_name) != 1) {
          bitvector_to_string.insert({field_name, {}});
        }
        bitvector_to_string.at(field_name)
            .insert({z3_value.to_string(), string_value});
      }
    }
    default: {
      if (BitVectorToStringTranslationMap().count(field_name) == 1) {
        return absl::InvalidArgumentError(absl::StrCat(
            "A table entry provides a non-string value ", value.DebugString(),
            "to a string translated field", field_name));
      }
      return Bmv2ValueZ3Expr(value);
    }
  }
}

// Exposes a static mapping from string values to bitvector values.
// We do not need to include field names here because we assume the string
// values are unique.
std::unordered_map<std::string, z3::expr> &StringToBitVectorTranslationMap() {
  static std::unordered_map<std::string, z3::expr> *string_to_bitvector_map =
      new std::unordered_map<std::string, z3::expr>();
  return *string_to_bitvector_map;
}

// Exposes a static mapping from field names and bitvector values to
// string values.
std::unordered_map<std::string, std::unordered_map<std::string, std::string>>
    &BitVectorToStringTranslationMap() {
  static std::unordered_map<std::string,
                            std::unordered_map<std::string, std::string>>
      *bitvector_to_string_map = new std::unordered_map<
          std::string, std::unordered_map<std::string, std::string>>();
  return *bitvector_to_string_map;
}

std::unordered_map<std::string, uint64_t> &FieldNameToStringCountMap() {
  static std::unordered_map<std::string, uint64_t>
      *field_name_to_string_count_map =
          new std::unordered_map<std::string, uint64_t>();
  return *field_name_to_string_count_map;
}

// Reverse translation of internal values from the p4/bmv2 value domain
// to the string domain of P4RT.
// If this is called on values belonging to fields without a
// @p4runtime_translation annotation, it is a no-op.
gutil::StatusOr<std::string> TranslateValueToString(
    const std::string field_name, const std::string &value) {
  auto &count_map = FieldNameToStringCountMap();
  if (count_map.count(field_name) == 1) {
    const auto &reverse_map = BitVectorToStringTranslationMap();
    if (reverse_map.count(field_name) == 1) {
      if (reverse_map.at(field_name).count(value) == 1) {
        return reverse_map.at(field_name).at(value);
      }
    }
    return absl::InvalidArgumentError(
        absl::StrCat("Cannot translate value ", value,
                     " to a string value for field ", field_name));
  }
  return value;
}

}  // namespace values
}  // namespace symbolic
}  // namespace p4_symbolic
