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

#include "p4_symbolic/symbolic/util.h"

#include <cstdint>
#include <locale>
#include <sstream>
#include <string>
#include <vector>

#include "absl/strings/match.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/strip.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/packet.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

namespace {

bool Z3BooltoBool(Z3_lbool z3_bool) {
  switch (z3_bool) {
    case Z3_L_TRUE:
      return true;
    default:
      return false;
  }
}

}  // namespace

gutil::StatusOr<std::unordered_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Loop over every header instance in the p4 program.
  // Find its type, and loop over every field in it, creating a symbolic free
  // variable for every field in every header instance.
  std::unordered_map<std::string, z3::expr> symbolic_headers;
  for (const auto &[header_name, header_type] : headers) {
    // Special validity field.
    std::string valid_field_name = absl::StrFormat("%s.$valid$", header_name);
    z3::expr valid_expression =
        Z3Context().bool_const(valid_field_name.c_str());
    symbolic_headers.insert({valid_field_name, valid_expression});

    // Regular fields defined in the p4 program or v1model.
    for (const auto &[field_name, field] : header_type.fields()) {
      if (field.signed_()) {
        return absl::UnimplementedError(
            "Negative header fields are not supported");
      }

      std::string field_full_name =
          absl::StrFormat("%s.%s", header_name, field_name);
      z3::expr field_expression =
          Z3Context().bv_const(field_full_name.c_str(), field.bitwidth());
      symbolic_headers.insert({field_full_name, field_expression});
    }
  }

  // Finally, we have a special field marking if the packet represented by
  // these headers was dropped.
  symbolic_headers.insert({"$dropped$", Z3Context().bool_val(false)});
  return symbolic_headers;
}

ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model) {
  // Extract ports.
  std::string ingress_port = model.eval(context.ingress_port, true).to_string();
  std::string egress_port = model.eval(context.egress_port, true).to_string();

  // Extract an input packet and its predicted output.
  ConcretePacket ingress_packet =
      packet::ExtractConcretePacket(context.ingress_packet, model);
  ConcretePacket egress_packet =
      packet::ExtractConcretePacket(context.egress_packet, model);

  // Extract the ingress and egress headers.
  ConcreteHeaders ingress_headers;
  for (const auto &[name, expr] : context.ingress_headers) {
    ingress_headers[name] = model.eval(expr, true).to_string();
  }
  ConcreteHeaders egress_headers;
  for (const auto &[name, expr] : context.egress_headers) {
    egress_headers[name] = model.eval(expr, true).to_string();
  }

  // Extract the trace (matches on every table).
  bool dropped =
      Z3BooltoBool(model.eval(context.trace.dropped, true).bool_value());
  std::unordered_map<std::string, ConcreteTableMatch> matches;
  for (const auto &[table, match] : context.trace.matched_entries) {
    matches[table] = {
        Z3BooltoBool(model.eval(match.matched, true).bool_value()),
        model.eval(match.entry_index, true).get_numeral_int(),
        model.eval(match.value, true).to_string()};
  }
  ConcreteTrace trace = {matches, dropped};

  return {ingress_port,    egress_port,    ingress_packet, egress_packet,
          ingress_headers, egress_headers, trace};
}

gutil::StatusOr<SymbolicTrace> MergeTracesOnCondition(
    const SymbolicTrace &original, const SymbolicTrace &changed,
    const z3::expr &condition) {
  SymbolicTrace merged = {{}, Z3Context().bool_val(false)};
  ASSIGN_OR_RETURN(merged.dropped, operators::Ite(condition, changed.dropped,
                                                  original.dropped));
  for (const auto &[name, changed_match] : changed.matched_entries) {
    // SymbolicTraces have the same set of tables always, similar to
    // SymbolicHeaders, accessing with .at() is safe here.
    const auto &original_match = original.matched_entries.at(name);

    ASSIGN_OR_RETURN(z3::expr merged_matched,
                     operators::Ite(condition, changed_match.matched,
                                    original_match.matched));
    ASSIGN_OR_RETURN(z3::expr merged_index,
                     operators::Ite(condition, changed_match.entry_index,
                                    original_match.entry_index));
    ASSIGN_OR_RETURN(
        z3::expr merged_value,
        operators::Ite(condition, changed_match.value, original_match.value));
    SymbolicTableMatch merged_match = {merged_matched, merged_index,
                                       merged_value};
    merged.matched_entries.insert({name, merged_match});
  }
  return merged;
}

gutil::StatusOr<z3::expr> IrValueToZ3Expr(const pdpi::IrValue &value) {
  switch (value.format_case()) {
    case pdpi::IrValue::kHexStr: {
      const std::string &hexstr = value.hex_str();

      uint64_t decimal;
      std::stringstream converter;
      converter << std::hex << hexstr;
      if (converter >> decimal) {
        unsigned int bitsize = 0;
        uint64_t pow = 1;
        while (bitsize <= 64 && pow < decimal) {
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
                                     << ((3 - i) * 8);
        ip += shifted_component;
      }
      return Z3Context().bv_val(std::to_string(ip).c_str(), 32);
    }

    default:
      return absl::UnimplementedError(
          absl::StrCat("Found unsupported value type ", value.DebugString()));
  }
}

gutil::StatusOr<pdpi::IrValue> StringToIrValue(std::string value) {
  // Format according to type.
  if (absl::StartsWith(value, "0x")) {
    return pdpi::FormattedStringToIrValue(value, pdpi::Format::HEX_STRING);
  } else {
    // Some unsupported format!
    return absl::InvalidArgumentError(
        absl::StrCat("Literal value \"", value, "\" has unknown format!"));
  }
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
