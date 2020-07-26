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

#include <string>
#include <unordered_map>

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

SymbolicPerPacketState FreeSymbolicPacketState() {
  // Port variables.
  TypedExpr ingress_port = TypedExpr(Z3Context().bv_const("ingress_port", 9));
  // TODO(babman): not to find some better encoding of "undefined".
  TypedExpr egress_port = TypedExpr(Z3Context().bv_val("111111111", 9));

  // Packet header variables.
  SymbolicHeader header = headers::FreeSymbolicHeader();

  // Default metadata.
  SymbolicMetadata metadata;
  metadata.insert({"standard_metadata.ingress_port", ingress_port});
  metadata.insert({"standard_metadata.egress_spec", egress_port});

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
      ASSIGN_OR_RETURN(std::string bits, pdpi::IrValueToByteString(value));
      std::cout << bits << std::endl;
      std::string encoded_bits;
      for (char b : bits) {
        encoded_bits +=
            static_cast<char>(static_cast<int>(b) + static_cast<int>('0'));
      }
      return TypedExpr(
          Z3Context().bv_val(encoded_bits.c_str(), encoded_bits.size()));
    }
    default:
      return absl::UnimplementedError(
          absl::StrCat("Found unsupported value type ", value.DebugString()));
  }
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
