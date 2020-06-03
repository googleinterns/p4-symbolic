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

// Forwarding Code
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    // set the port when the table is hit   
    action set_egress_spec(bit<9> port) {
        standard_metadata.egress_spec = port;
    }

    // define the port routing table
    table ports_exact {
        key = {
            // exact equality matching
            standard_metadata.ingress_port: exact;
        }
        actions = {
            set_egress_spec;
            NoAction;
        }
        size = 1024;
        default_action = NoAction;
    }    

    apply {
        ports_exact.apply();
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
