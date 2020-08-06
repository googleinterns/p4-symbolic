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

// Hardcodes the behavior of an interesting p4 parser that is part
// of the p4 program we are interested in.
// The hardcoded behavior sets the validity of certain header fields
// based on the fields in the packet, and sets the default values
// for local_metadata fields.

#include "p4_symbolic/symbolic/parser.h"

#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace parser {

gutil::StatusOr<std::vector<z3::expr>> EvaluateHardcodedParser(
    SymbolicPerPacketState *state) {
  std::vector<z3::expr> constraints;
  // Set initial values for certain special metadata fields.
  z3::expr true_guard = Z3Context().bool_val(true);
  if (state->ContainsKey("local_metadata.vrf_id")) {
    RETURN_IF_ERROR(state->Set("vrf_id", Z3Context().bv_val(0, 1), true_guard));
  }
  if (state->ContainsKey("local_metadata.l4_src_port")) {
    RETURN_IF_ERROR(state->Set("local_metadata.l4_src_port",
                               Z3Context().bv_val(0, 1), true_guard));
  }
  if (state->ContainsKey("local_metadata.l4_dst_port")) {
    RETURN_IF_ERROR(state->Set("local_metadata.l4_dst_port",
                               Z3Context().bv_val(0, 1), true_guard));
  }

  // Find out which headers the program supports.
  bool program_has_ipv4 = state->ContainsKey("ipv4.$valid$");
  bool program_has_ipv6 = state->ContainsKey("ipv6.$valid$");
  z3::expr ipv4_valid = Z3Context().bool_val(false);
  z3::expr ipv6_valid = Z3Context().bool_val(false);
  if (program_has_ipv4) {
    ASSIGN_OR_RETURN(ipv4_valid, state->Get("ipv4.$valid$"));
  }
  if (program_has_ipv6) {
    ASSIGN_OR_RETURN(ipv6_valid, state->Get("ipv6.$valid$"));
  }

  // Put restrictions on what "eth_type" can be and how it affects validity of
  // certain headers.
  if (state->ContainsKey("ethernet.ether_type")) {
    ASSIGN_OR_RETURN(z3::expr eth_type, state->Get("ethernet.ether_type"));

    if (program_has_ipv4) {
      constraints.push_back(ipv4_valid == (eth_type == ETHERTYPE_IPV4));
    }
    if (program_has_ipv6) {
      constraints.push_back(ipv6_valid == (eth_type == ETHERTYPE_IPV6));
    }
    if (state->ContainsKey("arp.$valid$")) {
      ASSIGN_OR_RETURN(z3::expr arp_valid, state->Get("arp.$valid$"));
      constraints.push_back(arp_valid == (eth_type == ETHERTYPE_ARP));
    }

    // Similar but for protocol used.
    if (program_has_ipv4 || program_has_ipv6) {
      if (state->ContainsKey("icmp.$valid$")) {
        ASSIGN_OR_RETURN(z3::expr icmp_valid, state->Get("icmp.$valid$"));
        z3::expr icmp_valid_constraint = Z3Context().bool_val(false);
        if (program_has_ipv4) {
          ASSIGN_OR_RETURN(z3::expr protocol, state->Get("ipv4.protocol"));
          z3::expr icmp_valid_ipv4 =
              (protocol == IP_PROTOCOL_ICMP) && ipv4_valid;
          icmp_valid_constraint = icmp_valid_constraint || icmp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr icmp_valid_ipv6 =
              (next_header == IP_PROTOCOL_ICMPV6) && ipv6_valid;
          icmp_valid_constraint = icmp_valid_constraint || icmp_valid_ipv6;
        }
        constraints.push_back(icmp_valid == icmp_valid_constraint);
      }
      if (state->ContainsKey("tcp.$valid$")) {
        ASSIGN_OR_RETURN(z3::expr tcp_valid, state->Get("tcp.$valid$"));

        z3::expr tcp_valid_constraint = Z3Context().bool_val(false);
        if (program_has_ipv4) {
          ASSIGN_OR_RETURN(z3::expr protocol, state->Get("ipv4.protocol"));
          z3::expr tcp_valid_ipv4 = (protocol == IP_PROTOCOL_TCP) && ipv4_valid;
          tcp_valid_constraint = tcp_valid_constraint || tcp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr tcp_valid_ipv6 =
              (next_header == IP_PROTOCOL_TCP) && ipv6_valid;
          tcp_valid_constraint = tcp_valid_constraint || tcp_valid_ipv6;
        }
        constraints.push_back(tcp_valid == tcp_valid_constraint);
        // Set l4_src_port and l4_dst_port to those of tcp header.
        if (state->ContainsKey("local_metadata.l4_src_port") &&
            state->ContainsKey("tcp.src_port")) {
          ASSIGN_OR_RETURN(z3::expr tcp_src_port, state->Get("tcp.src_port"));
          RETURN_IF_ERROR(state->Set("local_metadata.l4_src_port", tcp_src_port,
                                     tcp_valid));
        }
        if (state->ContainsKey("local_metadata.l4_dst_port") &&
            state->ContainsKey("tcp.dst_port")) {
          ASSIGN_OR_RETURN(z3::expr tcp_dst_port, state->Get("tcp.dst_port"));
          RETURN_IF_ERROR(state->Set("local_metadata.l4_dst_port", tcp_dst_port,
                                     tcp_valid));
        }
      }
      if (state->ContainsKey("udp.$valid$")) {
        ASSIGN_OR_RETURN(z3::expr udp_valid, state->Get("udp.$valid$"));

        z3::expr udp_valid_constraint = Z3Context().bool_val(false);
        if (program_has_ipv4) {
          ASSIGN_OR_RETURN(z3::expr protocol, state->Get("ipv4.protocol"));
          z3::expr udp_valid_ipv4 = (protocol == IP_PROTOCOL_UDP) && ipv4_valid;
          udp_valid_constraint = udp_valid_constraint || udp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr udp_valid_ipv6 =
              (next_header == IP_PROTOCOL_UDP) && ipv6_valid;
          udp_valid_constraint = udp_valid_constraint || udp_valid_ipv6;
        }
        constraints.push_back(udp_valid == udp_valid_constraint);
        // Set l4_src_port and l4_dst_port to those of udp header.
        if (state->ContainsKey("local_metadata.l4_src_port") &&
            state->ContainsKey("udp.src_port")) {
          ASSIGN_OR_RETURN(z3::expr udp_src_port, state->Get("udp.src_port"));
          RETURN_IF_ERROR(state->Set("local_metadata.l4_src_port", udp_src_port,
                                     udp_valid));
        }
        if (state->ContainsKey("local_metadata.l4_dst_port") &&
            state->ContainsKey("udp.dst_port")) {
          ASSIGN_OR_RETURN(z3::expr udp_dst_port, state->Get("udp.dst_port"));
          RETURN_IF_ERROR(state->Set("local_metadata.l4_dst_port", udp_dst_port,
                                     udp_valid));
        }
      }
    }
  }

  // Done, return all constraints.
  return constraints;
}

}  // namespace parser
}  // namespace symbolic
}  // namespace p4_symbolic
