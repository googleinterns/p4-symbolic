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

# This file contains rule definitions for running
# the test binary to produce output json and protobuf files,
# subset diff the input and output json files, and golden file
# testing the output protobuf files against the expected files.
# It also defines a Macro that simplifies defining a protobuf test
# over a sample P4 program.

load("//:p4c.bzl", "run_p4c")
load("//p4_symbolic/bmv2:test.bzl", "exact_diff_test")

# Macro that defines exact diff IR testing rules for a given p4 program
# with all their dependent rules.
# The macro defines these rules in order:
# 1. A rule for producing bmv2 json and p4info files from a .p4 file using p4c.
# 2. A rule for parsing the bmv2 json and p4info using p4_symbolic/main.cc, and
#    dumping a protobuf output file.
# 3. A rule for golden file testing of the protobuf output file against
#    the specified expected file.
# Use the p4_deps list to specify dependent files that p4_program input
# file depends on (e.g. by including them).
def ir_parsing_test(name, p4_program, golden_file, table_entries = None, p4_deps = []):
    p4c_name = "%s_p4c" % name
    parse_name = "%s_parse" % name
    p4info_file = "%s_bazel-p4c-tmp-output/p4info.pb.txt" % p4c_name

    optional_table_entries = []
    optional_table_entry_arg = ""
    if table_entries:
        optional_table_entries = [table_entries]
        optional_table_entry_arg = "--entries=$(location %s)" % table_entries

    # Run p4c to get bmv2 JSON and p4info.pb.txt files.
    run_p4c(
        name = p4c_name,
        src = p4_program,
        deps = p4_deps,
        p4runtime_files = [p4info_file],
    )

    # Use p4_symbolic/main.cc to parse input json with p4info and dump
    # (tmp) output .pb.txt.
    output_filename = name + "_tmp.pb.txt"
    native.genrule(
        name = parse_name,
        srcs = [":" + p4c_name, p4info_file] + optional_table_entries,
        outs = [output_filename],
        tools = ["//p4_symbolic/ir:test"],
        cmd = (
            "$(location //p4_symbolic/ir:test) --bmv2=$(location %s) " +
            "--p4info=$(location %s) %s &> $(OUTS) || true"
        ) % (":" + p4c_name, p4info_file, optional_table_entry_arg),
    )

    # Exact diff test between output and golden protobuf files.
    exact_diff_test(
        name = name,
        actual = output_filename,
        expected = golden_file,
    )
