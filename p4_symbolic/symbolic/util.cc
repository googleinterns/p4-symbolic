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

SymbolicTableMatch DefaultTableMatch() {
  return {
      Z3Context().bool_val(false),  // No match yet!
      Z3Context().int_val(-1)       // No match index.
  };
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
  ConcretePerPacketState ingress_headers;
  for (const auto &[name, expr] : context.ingress_headers) {
    ingress_headers[name] = model.eval(expr, true).to_string();
  }
  ConcretePerPacketState egress_headers;
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
        model.eval(match.entry_index, true).get_numeral_int()};
  }
  ConcreteTrace trace = {matches, dropped};

  return {ingress_port,    egress_port,    ingress_packet, egress_packet,
          ingress_headers, egress_headers, trace};
}

gutil::StatusOr<SymbolicTrace> MergeTracesOnCondition(
    const z3::expr &condition, const SymbolicTrace &true_trace,
    const SymbolicTrace &false_trace) {
  ASSIGN_OR_RETURN(
      z3::expr merged_dropped,
      operators::Ite(condition, true_trace.dropped, false_trace.dropped));

  // The merged trace is initially empty.
  SymbolicTrace merged = {{}, merged_dropped};

  // Merge all tables matches in true_trace (including ones in both traces).
  for (const auto &[name, true_match] : true_trace.matched_entries) {
    // Find match in other trace (or use default).
    SymbolicTableMatch false_match = DefaultTableMatch();
    if (false_trace.matched_entries.count(name) > 0) {
      false_match = false_trace.matched_entries.at(name);
    }

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.matched_entries.insert({name, {matched, index}});
  }

  // Merge all tables matches in false_trace only.
  for (const auto &[name, false_match] : false_trace.matched_entries) {
    SymbolicTableMatch true_match = DefaultTableMatch();
    if (true_trace.matched_entries.count(name) > 0) {
      continue;  // Already covered.
    }

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.matched_entries.insert({name, {matched, index}});
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

gutil::StatusOr<std::vector<z3::expr>> ParserConstraints(
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
      constraints.push_back(ipv4_valid == (eth_type == 0x800));
    }
    if (program_has_ipv6) {
      constraints.push_back(ipv6_valid == (eth_type == 0x86dd));
    }
    if (state->ContainsKey("arp.$valid$")) {
      ASSIGN_OR_RETURN(z3::expr arp_valid, state->Get("arp.$valid$"));
      constraints.push_back(arp_valid == (eth_type == 0x0806));
    }

    // Similar but for protocol used.
    if (program_has_ipv4 || program_has_ipv6) {
      if (state->ContainsKey("icmp.$valid$")) {
        ASSIGN_OR_RETURN(z3::expr icmp_valid, state->Get("icmp.$valid$"));
        z3::expr icmp_valid_constraint = Z3Context().bool_val(false);
        if (program_has_ipv4) {
          ASSIGN_OR_RETURN(z3::expr protocol, state->Get("ipv4.protocol"));
          z3::expr icmp_valid_ipv4 = (protocol == 0x01) && ipv4_valid;
          icmp_valid_constraint = icmp_valid_constraint || icmp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr icmp_valid_ipv6 = (next_header == 0x3a) && ipv6_valid;
          icmp_valid_constraint = icmp_valid_constraint || icmp_valid_ipv6;
        }
        constraints.push_back(icmp_valid == icmp_valid_constraint);
      }
      if (state->ContainsKey("tcp.$valid$")) {
        ASSIGN_OR_RETURN(z3::expr tcp_valid, state->Get("tcp.$valid$"));

        z3::expr tcp_valid_constraint = Z3Context().bool_val(false);
        if (program_has_ipv4) {
          ASSIGN_OR_RETURN(z3::expr protocol, state->Get("ipv4.protocol"));
          z3::expr tcp_valid_ipv4 = (protocol == 0x06) && ipv4_valid;
          tcp_valid_constraint = tcp_valid_constraint || tcp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr tcp_valid_ipv6 = (next_header == 0x06) && ipv6_valid;
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
          z3::expr udp_valid_ipv4 = (protocol == 0x11) && ipv4_valid;
          udp_valid_constraint = udp_valid_constraint || udp_valid_ipv4;
        }
        if (program_has_ipv6) {
          ASSIGN_OR_RETURN(z3::expr next_header,
                           state->Get("ipv6.next_header"));
          z3::expr udp_valid_ipv6 = (next_header == 0x11) && ipv6_valid;
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

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
