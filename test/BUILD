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

load("//:p4c.bzl", "run_p4c")
load("//test:bmv2_parsing_check.bzl",
     "subset_diff_test",
     "exact_diff_test",
     "parse_bmv2",
     "extract_output_group")


subset_diff_test(
    name = "port_table_subset_test",
    actual = ":port_table_parse_json",
    expected = ":port_table_p4c"
)

exact_diff_test(
    name = "port_table_exact_test",
    actual = ":port_table_parse_protobuf",
    expected = "expected/table.pb.txt"
)

extract_output_group(
    name = "port_table_parse_json",
    target = ":port_table_parse",
    output_group = "json"
)

extract_output_group(
    name = "port_table_parse_protobuf",
    target = ":port_table_parse",
    output_group = "protobuf"
)

parse_bmv2(
    name = "port_table_parse",
    input = ":port_table_p4c"
)

run_p4c(
  name = "port_table_p4c",
  p4program = "samples/port-table/table.p4"
)
