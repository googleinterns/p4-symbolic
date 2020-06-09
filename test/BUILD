# Copyright 2020 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# This file defines test rules for our protobuf definition of the
# bmv2 json format.
# We define one overall test rule per sample test P4 program (available under
# ./samples/**). Each test rule performs golden file testing against
# stored expected protobuf output (available under ./expected), and
# subset diff testing of the ouput json against the p4c bmv2 json build
# of the test program.

load("//:p4c.bzl", "run_p4c")
load("//test:bmv2_parsing_check.bzl", "bmv2_protobuf_parsing_test")

bmv2_protobuf_parsing_test(
    name = "port_table",
    p4_program = "samples/port-table/table.p4",
    golden_file = "expected/table.pb.txt"
)

bmv2_protobuf_parsing_test(
    name = "ipv4_routing",
    p4_program = "samples/ipv4-routing/basic.p4",
    golden_file = "expected/basic.pb.txt"
)

bmv2_protobuf_parsing_test(
    name = "port_hardcoded",
    p4_program = "samples/hardcoded/hardcoded.p4",
    golden_file = "expected/hardcoded.pb.txt"
)

bmv2_protobuf_parsing_test(
    name = "reflector",
    p4_program = "samples/reflector/reflector.p4",
    golden_file = "expected/reflector.pb.txt"
)
