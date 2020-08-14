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

/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

const bit<16> TYPE_IPV4 = 0x800;

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;

header ethernet_t {
  macAddr_t dstAddr;
  macAddr_t srcAddr;
  bit<16> etherType;
}
header ipv4_t {
  bit<4> version;
  bit<4> ihl;
  bit<8> diffserv;
  bit<16> totalLen;
  bit<16> identification;
  bit<3> flags;
  bit<13> fragOffset;
  bit<8> ttl;
  bit<8> protocol;
  bit<16> hdrChecksum;
  ip4Addr_t srcAddr;
  ip4Addr_t dstAddr;
}
struct headers {
  ethernet_t ethernet;
  ipv4_t ipv4;
}
struct local_metadata_t {
  bit<10> vrf;
  bool vrf_is_valid;
}

parser MyParser(packet_in packet, out headers hdr,
                inout local_metadata_t local_metadata,
                inout standard_metadata_t standard_metadata) {
  state start {
    transition parse_ethernet;
  }

  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition select(hdr.ethernet.etherType) {
      TYPE_IPV4: parse_ipv4;
      default: accept;
    }
  }

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition accept;
  }
}

// Ingress processing:
// First set vrf by matching on ipv4.srcAddr,
// then match on vrf and ipv4.dstAddr to route.
control MyIngress(inout headers hdr,
                  inout local_metadata_t local_metadata,
                  inout standard_metadata_t standard_metadata) {
  // NoAction: 21257015
  // 25652968
  action drop() {
    mark_to_drop(standard_metadata);
  }

  // 24959910
  action set_vrf(bit<10> vrf) {
    local_metadata.vrf = vrf;
    local_metadata.vrf_is_valid = true;
  }

  // 28792405
  action ipv4_forward(macAddr_t dstAddr, egressSpec_t port) {
    standard_metadata.egress_spec = port;
    hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
    hdr.ethernet.dstAddr = dstAddr;
    hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
  }

  // 37105383
  table set_vrf_table {
    key = {
      hdr.ipv4.srcAddr: ternary @format(IPV4_ADDRESS);
    }
    actions = {
      @proto_id(1) set_vrf;
      @proto_id(2) NoAction;
    }
    size = 1024;
    default_action = NoAction;
  }

  // 45604648
  table ipv4_lpm_table {
    key = {
      hdr.ipv4.dstAddr: lpm @format(IPV4_ADDRESS);
      local_metadata.vrf: exact;
    }
    actions = {
      @proto_id(1) ipv4_forward;
      @proto_id(2) drop;
    }
    size = 1024;
    default_action = drop();
  }

  apply {
    // vrf is not valid by default.
    local_metadata.vrf_is_valid = false;

    // Check that the packet is an ipv4 packet.
    if (hdr.ipv4.isValid()) {
      // Set a vrf.
      set_vrf_table.apply();
      if (local_metadata.vrf_is_valid) {
        // If vrf was set, do lpm matching on dst to route.
        ipv4_lpm_table.apply();
      }   
    }
  }
}

control MyDeparser(packet_out packet, in headers hdr) {
  apply {
    packet.emit(hdr.ethernet);
    packet.emit(hdr.ipv4);
  }
}

control MyEgress(inout headers hdr, inout local_metadata_t local_metadata,
                 inout standard_metadata_t standard_metadata) {
  apply {}
}


control MyComputeChecksum(inout headers hdr,
                          inout local_metadata_t local_metadata) {
  apply {}
}

control MyVerifyChecksum(inout headers hdr,
                         inout local_metadata_t local_metadata) {   
  apply {}
}

V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;
