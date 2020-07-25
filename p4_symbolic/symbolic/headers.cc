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
// symbolic header structs.

#include "p4_symbolic/symbolic/headers.h"

#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {
namespace headers {

SymbolicHeader FreeSymbolicHeader() {
  return {
      Z3Context().bv_const("ingress_eth_src", 48),
      Z3Context().bv_const("ingress_eth_dst", 48),
      Z3Context().bv_const("ingress_eth_type", 16),

      Z3Context().bv_const("ingress_outer_ipv4_src", 32),
      Z3Context().bv_const("ingress_outer_ipv4_dst", 32),
      Z3Context().bv_const("ingress_outer_ipv6_dst_upper", 64),
      Z3Context().bv_const("ingress_outer_ipv6_dst_lower", 64),
      Z3Context().bv_const("ingress_outer_protocol", 8),
      Z3Context().bv_const("ingress_outer_dscp", 6),
      Z3Context().bv_const("ingress_outer_ttl", 8),

      Z3Context().bv_const("ingress_inner_ipv4_dst", 32),
      Z3Context().bv_const("ingress_inner_ipv6_dst_upper", 64),
      Z3Context().bv_const("ingress_inner_ipv6_dst_lower", 64),
      Z3Context().bv_const("ingress_inner_protocol", 8),
      Z3Context().bv_const("ingress_inner_dscp", 6),
      Z3Context().bv_const("ingress_inner_ttl", 8),

      Z3Context().bv_const("ingress_icmp_type", 8),
      Z3Context().bv_const("ingress_vid", 12),
  };
}

ConcreteHeader ExtractConcreteHeaders(SymbolicHeader header, z3::model model) {
  return {model.eval(header.eth_src, true).to_string(),
          model.eval(header.eth_dst, true).to_string(),
          model.eval(header.eth_type, true).to_string(),

          model.eval(header.outer_ipv4_src, true).to_string(),
          model.eval(header.outer_ipv4_dst, true).to_string(),
          model.eval(header.outer_ipv6_dst_upper, true).to_string(),
          model.eval(header.outer_ipv6_dst_lower, true).to_string(),
          model.eval(header.outer_protocol, true).to_string(),
          model.eval(header.outer_dscp, true).to_string(),
          model.eval(header.outer_ttl, true).to_string(),

          model.eval(header.inner_ipv4_dst, true).to_string(),
          model.eval(header.inner_ipv6_dst_upper, true).to_string(),
          model.eval(header.inner_ipv6_dst_lower, true).to_string(),
          model.eval(header.inner_protocol, true).to_string(),
          model.eval(header.inner_dscp, true).to_string(),
          model.eval(header.inner_ttl, true).to_string(),

          model.eval(header.icmp_type, true).to_string(),
          model.eval(header.vid, true).to_string()};
}

SymbolicHeader MergeHeadersOnCondition(const SymbolicHeader &original,
                                       const SymbolicHeader &changed,
                                       const z3::expr &condition) {
  return {util::MergeExpressionsWithCondition(original.eth_src, changed.eth_src,
                                              condition),
          util::MergeExpressionsWithCondition(original.eth_dst, changed.eth_dst,
                                              condition),
          util::MergeExpressionsWithCondition(original.eth_type,
                                              changed.eth_type, condition),

          util::MergeExpressionsWithCondition(
              original.outer_ipv4_src, changed.outer_ipv4_src, condition),
          util::MergeExpressionsWithCondition(
              original.outer_ipv4_dst, changed.outer_ipv4_dst, condition),
          util::MergeExpressionsWithCondition(original.outer_ipv6_dst_upper,
                                              changed.outer_ipv6_dst_upper,
                                              condition),
          util::MergeExpressionsWithCondition(original.outer_ipv6_dst_lower,
                                              changed.outer_ipv6_dst_lower,
                                              condition),
          util::MergeExpressionsWithCondition(
              original.outer_protocol, changed.outer_protocol, condition),
          util::MergeExpressionsWithCondition(original.outer_dscp,
                                              changed.outer_dscp, condition),
          util::MergeExpressionsWithCondition(original.outer_ttl,
                                              changed.outer_ttl, condition),

          util::MergeExpressionsWithCondition(
              original.inner_ipv4_dst, changed.inner_ipv4_dst, condition),
          util::MergeExpressionsWithCondition(original.inner_ipv6_dst_upper,
                                              changed.inner_ipv6_dst_upper,
                                              condition),
          util::MergeExpressionsWithCondition(original.inner_ipv6_dst_lower,
                                              changed.inner_ipv6_dst_lower,
                                              condition),
          util::MergeExpressionsWithCondition(
              original.inner_protocol, changed.inner_protocol, condition),
          util::MergeExpressionsWithCondition(original.inner_dscp,
                                              changed.inner_dscp, condition),
          util::MergeExpressionsWithCondition(original.inner_ttl,
                                              changed.inner_ttl, condition),

          util::MergeExpressionsWithCondition(original.icmp_type,
                                              changed.icmp_type, condition),
          util::MergeExpressionsWithCondition(original.vid, changed.vid,
                                              condition)};
}

}  // namespace headers
}  // namespace symbolic
}  // namespace p4_symbolic
