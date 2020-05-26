/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

struct metadata {}
struct headers {}

parser UselessParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control UselessChecksum(inout headers hdr, inout metadata meta) {   
    apply {  }
}

control UselessEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control UselessComputeChecksum(inout headers  hdr, inout metadata meta) {
    apply { }
}

control UselessDeparser(packet_out packet, in headers hdr) {
    apply { }
}

// Reflecting Packets Code
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {    
    apply {
        standard_metadata.egress_spec = standard_metadata.ingress_port;
    }
}

// Switch
V1Switch(
    UselessParser(),
    UselessChecksum(),
    MyIngress(),
    UselessEgress(),
    UselessComputeChecksum(),
    UselessDeparser()
) main;
