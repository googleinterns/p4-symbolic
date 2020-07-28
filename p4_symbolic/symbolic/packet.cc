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

#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {
namespace packet {

SymbolicPacket ExtractSymbolicPacket(SymbolicHeaders headers) {
  // TODO(babman): extract the packet fields from their metadata counterpart.
  return {
      TypedExpr(Z3Context().bv_const("ingress_eth_src", 48)),
      TypedExpr(Z3Context().bv_const("ingress_eth_dst", 48)),
      TypedExpr(Z3Context().bv_const("ingress_eth_type", 16)),

      TypedExpr(Z3Context().bv_const("ingress_outer_ipv4_src", 32)),
      TypedExpr(Z3Context().bv_const("ingress_outer_ipv4_dst", 32)),
      TypedExpr(Z3Context().bv_const("ingress_outer_ipv6_dst_upper", 64)),
      TypedExpr(Z3Context().bv_const("ingress_outer_ipv6_dst_lower", 64)),
      TypedExpr(Z3Context().bv_const("ingress_outer_protocol", 8)),
      TypedExpr(Z3Context().bv_const("ingress_outer_dscp", 6)),
      TypedExpr(Z3Context().bv_const("ingress_outer_ttl", 8)),

      TypedExpr(Z3Context().bv_const("ingress_inner_ipv4_dst", 32)),
      TypedExpr(Z3Context().bv_const("ingress_inner_ipv6_dst_upper", 64)),
      TypedExpr(Z3Context().bv_const("ingress_inner_ipv6_dst_lower", 64)),
      TypedExpr(Z3Context().bv_const("ingress_inner_protocol", 8)),
      TypedExpr(Z3Context().bv_const("ingress_inner_dscp", 6)),
      TypedExpr(Z3Context().bv_const("ingress_inner_ttl", 8)),

      TypedExpr(Z3Context().bv_const("ingress_icmp_type", 8)),
      TypedExpr(Z3Context().bv_const("ingress_vid", 12)),
  };
}

ConcretePacket ExtractConcretePacket(SymbolicPacket packet, z3::model model) {
  return {model.eval(packet.eth_src.expr(), true).to_string(),
          model.eval(packet.eth_dst.expr(), true).to_string(),
          model.eval(packet.eth_type.expr(), true).to_string(),

          model.eval(packet.outer_ipv4_src.expr(), true).to_string(),
          model.eval(packet.outer_ipv4_dst.expr(), true).to_string(),
          model.eval(packet.outer_ipv6_dst_upper.expr(), true).to_string(),
          model.eval(packet.outer_ipv6_dst_lower.expr(), true).to_string(),
          model.eval(packet.outer_protocol.expr(), true).to_string(),
          model.eval(packet.outer_dscp.expr(), true).to_string(),
          model.eval(packet.outer_ttl.expr(), true).to_string(),

          model.eval(packet.inner_ipv4_dst.expr(), true).to_string(),
          model.eval(packet.inner_ipv6_dst_upper.expr(), true).to_string(),
          model.eval(packet.inner_ipv6_dst_lower.expr(), true).to_string(),
          model.eval(packet.inner_protocol.expr(), true).to_string(),
          model.eval(packet.inner_dscp.expr(), true).to_string(),
          model.eval(packet.inner_ttl.expr(), true).to_string(),

          model.eval(packet.icmp_type.expr(), true).to_string(),
          model.eval(packet.vid.expr(), true).to_string()};
}

}  // namespace packet
}  // namespace symbolic
}  // namespace p4_symbolic
