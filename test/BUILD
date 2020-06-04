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

load("//test:bmv2_parsing_check.bzl", "subset_diff_test")
load("//:p4c.bzl", "run_p4c")

# subset diff tests that check
# dumped parsed json is a subset of p4c output json
subset_diff_test(
    name = "port_table_test",
    input = ":p4c_table"
)

subset_diff_test(
    name = "hardcoded_test",
    input = ":p4c_hardcoded"
)

subset_diff_test(
    name = "reflector_test",
    input = ":p4c_reflector"
)

subset_diff_test(
    name = "ipv4_test",
    input = ":p4c_ipv4"
)

# rules for compiling p4 programs to bmv2 json files
run_p4c(
  name = "p4c_table",
  p4program = "samples/port-table/table.p4"
)

run_p4c(
  name = "p4c_hardcoded",
  p4program = "samples/hardcoded/hardcoded.p4"
)

run_p4c(
  name = "p4c_reflector",
  p4program = "samples/reflector/reflector.p4"
)

run_p4c(
  name = "p4c_ipv4",
  p4program = "samples/ipv4-routing/basic.p4"
)
