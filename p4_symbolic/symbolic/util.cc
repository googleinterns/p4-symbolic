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

// Helpful utilities for managing symbolic and concrete states.

#include "p4_symbolic/symbolic/util.h"

#include <cstdint>
#include <locale>
#include <sstream>
#include <string>
#include <unordered_map>

#include "absl/strings/match.h"
#include "absl/strings/str_format.h"
#include "absl/strings/strip.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/headers.h"

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

SymbolicPerPacketState FreeSymbolicPacketState(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Packet header variables.
  SymbolicHeader header = headers::FreeSymbolicHeader();

  // Metadata fields.
  SymbolicMetadata metadata;
  for (const auto &[header_name, header_type] : headers) {
    // Special validity field.
    std::string valid_field_name = absl::StrFormat("%s.$valid$", header_name);
    TypedExpr valid_expression =
        TypedExpr(Z3Context().bool_const(valid_field_name.c_str()));
    metadata.insert({valid_field_name, valid_expression});

    // Regular fields defined in the p4 program or v1model.
    for (const auto &[field_name, field] : header_type.fields()) {
      std::string field_full_name =
          absl::StrFormat("%s.%s", header_name, field_name);
      TypedExpr field_expression = TypedExpr(
          Z3Context().bv_const(field_full_name.c_str(), field.bitwidth()),
          field.signed_());
      metadata.insert({field_full_name, field_expression});
    }
  }

  return {header, metadata};
}

ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model) {
  // Extract ports.
  std::string ingress_port =
      model.eval(context.ingress_port.expr(), true).to_string();
  std::string egress_port =
      model.eval(context.egress_port.expr(), true).to_string();

  // Extract an input packet and its predicted output.
  ConcreteHeader ingress_packet =
      headers::ExtractConcreteHeaders(context.ingress_packet, model);
  ConcreteHeader egress_packet =
      headers::ExtractConcreteHeaders(context.egress_packet, model);

  // Extract the last predicited value assigned to every metadata field when the
  // program is run on the input packet.
  ConcreteMetadata metadata;
  for (const auto &[name, expr] : context.metadata) {
    metadata[name] = model.eval(expr.expr(), true).to_string();
  }

  // Extract the trace (matches on every table).
  bool dropped =
      Z3BooltoBool(model.eval(context.trace.dropped.expr(), true).bool_value());
  std::unordered_map<std::string, ConcreteTableMatch> matches;
  for (const auto &[table, match] : context.trace.matched_entries) {
    matches[table] = {
        Z3BooltoBool(model.eval(match.matched.expr(), true).bool_value()),
        model.eval(match.entry_index.expr(), true).get_numeral_int(),
        model.eval(match.value.expr(), true).to_string()};
  }
  ConcreteTrace trace = {matches, dropped};

  return {ingress_port,  egress_port, ingress_packet,
          egress_packet, metadata,    trace};
}

TypedExpr MergeExpressionsWithCondition(const TypedExpr &original,
                                        const TypedExpr &changed,
                                        const TypedExpr &condition) {
  if (z3::eq(original.expr(), changed.expr())) {
    return original;
  }
  return TypedExpr::ite(condition, changed, original);
}

SymbolicPerPacketState MergeStatesOnCondition(
    const SymbolicPerPacketState &original,
    const SymbolicPerPacketState &changed, const TypedExpr &condition) {
  // Merge the header.
  SymbolicHeader merged_header = headers::MergeHeadersOnCondition(
      original.header, changed.header, condition);

  // Merge metadata.
  SymbolicMetadata merged_metadata;
  for (const auto &[name, expr] : changed.metadata) {
    if (original.metadata.count(name) == 1) {
      merged_metadata.insert(
          {name, MergeExpressionsWithCondition(original.metadata.at(name), expr,
                                               condition)});
    } else {
      merged_metadata.insert(
          {name, MergeExpressionsWithCondition(
                     TypedExpr(Z3Context().int_val(-1)), expr, condition)});
    }
  }

  return {merged_header, merged_metadata};
}

gutil::StatusOr<TypedExpr> IrValueToZ3Expr(const pdpi::IrValue &value) {
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

        auto result = TypedExpr(
            Z3Context().bv_val(std::to_string(decimal).c_str(), bitsize));
        return result;
      }

      return absl::InvalidArgumentError(absl::StrCat(
          "Cannot process hex string \"", hexstr, "\", the value is too big!"));
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
