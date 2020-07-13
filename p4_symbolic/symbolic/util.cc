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

}  // namespace

SymbolicContext FreeSymbolicContext(z3::context *z3_context) {
  // Port variables.
  z3::expr ingress_port = z3_context->int_const("ingress_port");
  z3::expr egress_port = z3_context->int_const("egress_port");

  // Packet header variables.
  SymbolicHeader ingress_packet = {
      z3_context->int_const("ingress_eth_src"),
      z3_context->int_const("ingress_eth_dst"),
      z3_context->int_const("ingress_eth_type"),

      z3_context->int_const("ingress_outer_ipv4_src"),
      z3_context->int_const("ingress_outer_ipv4_dst"),
      z3_context->int_const("ingress_outer_ipv6_dst_upper"),
      z3_context->int_const("ingress_outer_ipv6_dst_lower"),
      z3_context->int_const("ingress_outer_protocol"),
      z3_context->int_const("ingress_outer_dscp"),
      z3_context->int_const("ingress_outer_ttl"),

      z3_context->int_const("ingress_inner_ipv4_dst"),
      z3_context->int_const("ingress_inner_ipv6_dst_upper"),
      z3_context->int_const("ingress_inner_ipv6_dst_lower"),
      z3_context->int_const("ingress_inner_protocol"),
      z3_context->int_const("ingress_inner_dscp"),
      z3_context->int_const("ingress_inner_ttl"),

      z3_context->int_const("ingress_icmp_type"),
      z3_context->int_const("ingress_vid"),
  };

  SymbolicHeader egress_packet = {
      z3_context->int_const("egress_eth_src"),
      z3_context->int_const("egress_eth_dst"),
      z3_context->int_const("egress_eth_type"),

      z3_context->int_const("egress_outer_ipv4_src"),
      z3_context->int_const("egress_outer_ipv4_dst"),
      z3_context->int_const("egress_outer_ipv6_dst_upper"),
      z3_context->int_const("egress_outer_ipv6_dst_lower"),
      z3_context->int_const("egress_outer_protocol"),
      z3_context->int_const("egress_outer_dscp"),
      z3_context->int_const("egress_outer_ttl"),

      z3_context->int_const("egress_inner_ipv4_dst"),
      z3_context->int_const("egress_inner_ipv6_dst_upper"),
      z3_context->int_const("egress_inner_ipv6_dst_lower"),
      z3_context->int_const("egress_inner_protocol"),
      z3_context->int_const("egress_inner_dscp"),
      z3_context->int_const("egress_inner_ttl"),

      z3_context->int_const("egress_icmp_type"),
      z3_context->int_const("egress_vid"),
  };

  // Empty metadata and symbolic trace.
  SymbolicMetadata metadata;
  SymbolicTrace trace = {std::unordered_map<std::string, SymbolicTableMatch>(),
                         z3_context->bool_val(false)};

  return {ingress_port,  egress_port, ingress_packet,
          egress_packet, metadata,    trace};
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

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
