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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#include "p4_symbolic/symbolic/util.h"

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

ConcreteHeader ExtractConcreteFromSymbolicHeaders(SymbolicHeader header,
                                                  z3::model model) {
  return {model.eval(header.eth_src, true).get_numeral_int(),
          model.eval(header.eth_dst, true).get_numeral_int(),
          model.eval(header.eth_type, true).get_numeral_int(),

          model.eval(header.outer_ipv4_src, true).get_numeral_int(),
          model.eval(header.outer_ipv4_dst, true).get_numeral_int(),
          model.eval(header.outer_ipv6_dst_upper, true).get_numeral_int(),
          model.eval(header.outer_ipv6_dst_lower, true).get_numeral_int(),
          model.eval(header.outer_protocol, true).get_numeral_int(),
          model.eval(header.outer_dscp, true).get_numeral_int(),
          model.eval(header.outer_ttl, true).get_numeral_int(),

          model.eval(header.inner_ipv4_dst, true).get_numeral_int(),
          model.eval(header.inner_ipv6_dst_upper, true).get_numeral_int(),
          model.eval(header.inner_ipv6_dst_lower, true).get_numeral_int(),
          model.eval(header.inner_protocol, true).get_numeral_int(),
          model.eval(header.inner_dscp, true).get_numeral_int(),
          model.eval(header.inner_ttl, true).get_numeral_int(),

          model.eval(header.icmp_type, true).get_numeral_int(),
          model.eval(header.vid, true).get_numeral_int()};
}

z3::expr MergeExpressionWithCondition(const z3::expr &original,
                                      const z3::expr &changed,
                                      const z3::expr &condition) {
  if (z3::eq(original, changed)) {
    return original;
  }
  return z3::ite(condition, changed, original);
}

}  // namespace

SymbolicPerPacketState FreeSymbolicPacketState() {
  // Port variables.
  z3::expr ingress_port = Z3_CONTEXT->int_const("ingress_port");

  // Packet header variables.
  SymbolicHeader header = {
      Z3_CONTEXT->int_const("ingress_eth_src"),
      Z3_CONTEXT->int_const("ingress_eth_dst"),
      Z3_CONTEXT->int_const("ingress_eth_type"),

      Z3_CONTEXT->int_const("ingress_outer_ipv4_src"),
      Z3_CONTEXT->int_const("ingress_outer_ipv4_dst"),
      Z3_CONTEXT->int_const("ingress_outer_ipv6_dst_upper"),
      Z3_CONTEXT->int_const("ingress_outer_ipv6_dst_lower"),
      Z3_CONTEXT->int_const("ingress_outer_protocol"),
      Z3_CONTEXT->int_const("ingress_outer_dscp"),
      Z3_CONTEXT->int_const("ingress_outer_ttl"),

      Z3_CONTEXT->int_const("ingress_inner_ipv4_dst"),
      Z3_CONTEXT->int_const("ingress_inner_ipv6_dst_upper"),
      Z3_CONTEXT->int_const("ingress_inner_ipv6_dst_lower"),
      Z3_CONTEXT->int_const("ingress_inner_protocol"),
      Z3_CONTEXT->int_const("ingress_inner_dscp"),
      Z3_CONTEXT->int_const("ingress_inner_ttl"),

      Z3_CONTEXT->int_const("ingress_icmp_type"),
      Z3_CONTEXT->int_const("ingress_vid"),
  };

  // Default metadata.
  SymbolicMetadata metadata;
  metadata.insert({"standard_metadata.ingress_port", ingress_port});
  metadata.insert({"standard_metadata.egress_spec", Z3_CONTEXT->int_val(-1)});

  return {header, metadata};
}

ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model) {
  // Extract ports.
  int ingress_port = model.eval(context.ingress_port, true).get_numeral_int();
  int egress_port = model.eval(context.egress_port, true).get_numeral_int();

  // Extract an input packet and its predicted output.
  ConcreteHeader ingress_packet =
      ExtractConcreteFromSymbolicHeaders(context.ingress_packet, model);
  ConcreteHeader egress_packet =
      ExtractConcreteFromSymbolicHeaders(context.egress_packet, model);

  // Extract the last predicited value assigned to every metadata field when the
  // program is run on the input packet.
  ConcreteMetadata metadata;
  for (const auto &[name, expr] : context.metadata) {
    metadata[name] = model.eval(expr, true).get_numeral_int();
  }

  // Extract the trace (matches on every table).
  bool dropped =
      Z3BooltoBool(model.eval(context.trace.dropped, true).bool_value());
  std::unordered_map<std::string, ConcreteTableMatch> matches;
  for (const auto &[table, match] : context.trace.matched_entries) {
    matches[table] = {
        Z3BooltoBool(model.eval(match.matched, true).bool_value()),
        model.eval(match.entry_index, true).get_numeral_int(),
        model.eval(match.value, true).get_numeral_int()};
  }
  ConcreteTrace trace = {matches, dropped};

  return {ingress_port,  egress_port, ingress_packet,
          egress_packet, metadata,    trace};
}

SymbolicPerPacketState MergeStatesOnCondition(
    const SymbolicPerPacketState &original,
    const SymbolicPerPacketState &changed, const z3::expr &condition) {
  // Merge the header.
  SymbolicHeader merged_header = {
      MergeExpressionWithCondition(original.header.eth_src,
                                   changed.header.eth_src, condition),
      MergeExpressionWithCondition(original.header.eth_dst,
                                   changed.header.eth_dst, condition),
      MergeExpressionWithCondition(original.header.eth_type,
                                   changed.header.eth_type, condition),

      MergeExpressionWithCondition(original.header.outer_ipv4_src,
                                   changed.header.outer_ipv4_src, condition),
      MergeExpressionWithCondition(original.header.outer_ipv4_dst,
                                   changed.header.outer_ipv4_dst, condition),
      MergeExpressionWithCondition(original.header.outer_ipv6_dst_upper,
                                   changed.header.outer_ipv6_dst_upper,
                                   condition),
      MergeExpressionWithCondition(original.header.outer_ipv6_dst_lower,
                                   changed.header.outer_ipv6_dst_lower,
                                   condition),
      MergeExpressionWithCondition(original.header.outer_protocol,
                                   changed.header.outer_protocol, condition),
      MergeExpressionWithCondition(original.header.outer_dscp,
                                   changed.header.outer_dscp, condition),
      MergeExpressionWithCondition(original.header.outer_ttl,
                                   changed.header.outer_ttl, condition),

      MergeExpressionWithCondition(original.header.inner_ipv4_dst,
                                   changed.header.inner_ipv4_dst, condition),
      MergeExpressionWithCondition(original.header.inner_ipv6_dst_upper,
                                   changed.header.inner_ipv6_dst_upper,
                                   condition),
      MergeExpressionWithCondition(original.header.inner_ipv6_dst_lower,
                                   changed.header.inner_ipv6_dst_lower,
                                   condition),
      MergeExpressionWithCondition(original.header.inner_protocol,
                                   changed.header.inner_protocol, condition),
      MergeExpressionWithCondition(original.header.inner_dscp,
                                   changed.header.inner_dscp, condition),
      MergeExpressionWithCondition(original.header.inner_ttl,
                                   changed.header.inner_ttl, condition),

      MergeExpressionWithCondition(original.header.icmp_type,
                                   changed.header.icmp_type, condition),
      MergeExpressionWithCondition(original.header.vid, changed.header.vid,
                                   condition)};

  // Merge metadata.
  SymbolicMetadata merged_metadata;
  for (const auto &[name, expr] : changed.metadata) {
    z3::expr original_expr = Z3_CONTEXT->int_val(-1);
    if (original.metadata.count(name) == 1) {
      original_expr = original.metadata.at(name);
    }
    merged_metadata.insert(
        {name, MergeExpressionWithCondition(original_expr, expr, condition)});
  }

  return {merged_header, merged_metadata};
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
