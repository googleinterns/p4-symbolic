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

# Macro that defines our end to end tests.
# Given a p4 program, this macro runs our main binary
# on the p4 program and its table entries (if they exist).
# The binary outputs a debugging dump of the underlying smt program,
# as well as the output test packets.
# The macro compares both of these outputs against the provided
# expected golden files.
# The macro defines these rules in order:
# 1. A rule for producing bmv2 json and p4info files from a .p4 file using p4c.
# 2. A rule for running the main binary on the inputs using p4_symbolic/main.cc,
#    and dumping both output files.
# 3. Two rules for golden file testing of the two output files.
# 4. A test suite combining the two rules above with the same name
#    as given to the macro.
# Use the p4_deps list to specify dependent files that p4_program input
# file depends on (e.g. by including them).
def end_to_end_test(
        name,
        p4_program,
        output_golden_file,
        smt_golden_file,
        table_entries = None,
        p4_deps = []):
    p4c_name = "%s_p4c" % name
    run_name = "%s_main" % name
    p4info_file = "%s_bazel-p4c-tmp-output/p4info.pb.txt" % p4c_name
    output_test_name = "%s_output" % name
    smt_test_name = "%s_smt" % name

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

    # Use p4_symbolic/main.cc to run our tool on the p4 program
    # and produce a debugging smt file and an output file with
    # interesting testing packets.
    output_filename = name + ".txt"
    output_smt_filename = name + ".smt2"
    native.genrule(
        name = run_name,
        srcs = [":" + p4c_name, p4info_file] + optional_table_entries,
        outs = [output_filename, output_smt_filename],
        tools = ["//p4_symbolic:main"],
        cmd = (
            "$(location //p4_symbolic:main) --bmv2=$(location %s) " +
            "--p4info=$(location %s) %s --debug=$(location %s) " +
            "--hardcoded_parser=false &> $(location %s)"
        ) % (
            ":" + p4c_name,
            p4info_file,
            optional_table_entry_arg,
            output_smt_filename,
            output_filename,
        ),
    )

    # Exact diff test for the packet output file.
    exact_diff_test(
        name = output_test_name,
        actual = output_filename,
        expected = output_golden_file,
    )

    # Exact diff test for the smt output file.
    exact_diff_test(
        name = smt_test_name,
        actual = output_smt_filename,
        expected = smt_golden_file,
    )

    # Group tests into a test_suite with the given name.
    # This is just to make the provided name alias to something.
    native.test_suite(
        name = name,
        tests = [
            ":" + output_test_name,
            ":" + smt_test_name,
        ],
    )
