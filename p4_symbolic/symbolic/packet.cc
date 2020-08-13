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

// Contains helpers for creating, extracting, and managing concerete and
// symbolic packet structs.

#include "p4_symbolic/symbolic/packet.h"

#include <string>

namespace p4_symbolic {
namespace symbolic {
namespace packet {

namespace {

// Get the symbolic field value from state or return a default value
// of the given size.
z3::expr GetOrDefault(SymbolicPerPacketState state, const std::string &field,
                      unsigned int default_value_bit_size) {
  if (state.ContainsKey(field)) {
    return state.Get(field).value();
  }
  return Z3Context().bv_val(-1, default_value_bit_size);
}

}  // namespace

SymbolicPacket ExtractSymbolicPacket(SymbolicPerPacketState state) {
  z3::expr ipv6_dst = GetOrDefault(state, "ipv6.dst_addr", 128);

  return {GetOrDefault(state, "ethernet.src_addr", 48),
          GetOrDefault(state, "ethernet.dst_addr", 48),
          GetOrDefault(state, "ethernet.ether_type", 16),

          GetOrDefault(state, "ipv4.src_addr", 32),
          GetOrDefault(state, "ipv4.dst_addr", 32),
          ipv6_dst.extract(127, 64),
          ipv6_dst.extract(63, 0),
          GetOrDefault(state, "ipv4.protocol", 8),
          GetOrDefault(state, "ipv4.dscp", 6),
          GetOrDefault(state, "ipv4.ttl", 8),

          GetOrDefault(state, "icmp.type", 8)};
}

gutil::StatusOr<ConcretePacket> ExtractConcretePacket(
    SymbolicPacket packet, z3::model model,
    const values::ValueFormatter &value_formatter) {
  ASSIGN_OR_RETURN(
      std::string src_addr,
      value_formatter.TranslateValueToString(
          "ethernet.src_addr", model.eval(packet.eth_src, true).to_string()));
  ASSIGN_OR_RETURN(
      std::string dst_addr,
      value_formatter.TranslateValueToString(
          "ethernet.dst_addr", model.eval(packet.eth_dst, true).to_string()));
  ASSIGN_OR_RETURN(std::string ether_type,
                   value_formatter.TranslateValueToString(
                       "ethernet.ether_type",
                       model.eval(packet.eth_type, true).to_string()));

  ASSIGN_OR_RETURN(
      std::string ipv4_src_addr,
      value_formatter.TranslateValueToString(
          "ipv4.src_addr", model.eval(packet.ipv4_src, true).to_string()));
  ASSIGN_OR_RETURN(
      std::string ipv4_dst_addr,
      value_formatter.TranslateValueToString(
          "ipv4.dst_addr", model.eval(packet.ipv4_dst, true).to_string()));

  // Lower and upper ipv6_dst cant have string translations since they
  // are not whole values!
  std::string ipv6_dst_upper =
      model.eval(packet.ipv6_dst_upper, true).to_string();
  std::string ipv6_dst_lower =
      model.eval(packet.ipv6_dst_lower, true).to_string();

  // Remaining fields may have string translation.
  ASSIGN_OR_RETURN(
      std::string protocol,
      value_formatter.TranslateValueToString(
          "ipv4.protocol", model.eval(packet.protocol, true).to_string()));
  ASSIGN_OR_RETURN(std::string dscp,
                   value_formatter.TranslateValueToString(
                       "ipv4.dscp", model.eval(packet.dscp, true).to_string()));
  ASSIGN_OR_RETURN(std::string ttl,
                   value_formatter.TranslateValueToString(
                       "ipv4.ttl", model.eval(packet.ttl, true).to_string()));

  ASSIGN_OR_RETURN(
      std::string icmp_type,
      value_formatter.TranslateValueToString(
          "icmp.type", model.eval(packet.icmp_type, true).to_string()));

  return ConcretePacket{
      src_addr,       dst_addr,       ether_type, ipv4_src_addr, ipv4_dst_addr,
      ipv6_dst_upper, ipv6_dst_lower, protocol,   dscp,          ttl,
      icmp_type};
}

}  // namespace packet
}  // namespace symbolic
}  // namespace p4_symbolic
