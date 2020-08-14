#!/bin/bash
make build && cd ../../ && bazel build //p4_symbolic:main && ./bazel-bin/p4_symbolic/main --bmv2=p4-samples/vrf-routing/vrf.json --p4info=p4-samples/vrf-routing/vrf.pb.txt --entries=p4-samples/vrf-routing/entries.pb.txt --nohardcoded_parser
