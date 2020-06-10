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

# Golden file testing.
# Performs a simple diff between two files.
# Updates the  golden file when "--update"
# is passed via the command line.
# Note that the golden files are stored in the project, and not in the sandbox.
def _exact_diff_impl(ctx):
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = """
            # if user specifies --update option
            # we should generated the actual file and save it
            # as the expected file for future tests
            if [[ "$1" == "--update" ]]; then
                cp -f "{actual}" "${{BUILD_WORKSPACE_DIRECTORY}}/{expected}"
                exit 0
            fi

            # ensure expected file was previously generated
            if [ ! -f "{expected}" ]; then
                echo "Expected file \"{expected}\" does not exist."
                echo "run \"bazel run //{package}:{name} -- --update" first."
                exit 1
            fi

            # diff expected file with actual file
            diff -u "{expected}" "{actual}"
            if [[ $? = 0 ]]; then
                echo "PASSED"
                exit 0
            else
                echo "FAILED: Expected and actual differ."
                exit 1
            fi
        """.format(
            actual = ctx.file.actual.short_path,
            expected = ctx.file.expected.short_path,
            package = ctx.label.package,
            name = ctx.label.name,
        ),
    )

    runfiles = [ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles),
    )

exact_diff_test = rule(
    doc = """
        Computes diff of two files, fails if they disagree.
        Takes two attributes that represent the files to compare, or rules
        producing them.
        """,
    implementation = _exact_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = """
                The 'Actual' file.
                Typically the output of some command.
                """,
            mandatory = True,
            allow_single_file = True,
        ),
        "expected": attr.label(
            doc = "Expected file (aka golden file).",
            mandatory = True,
            allow_single_file = True,
        ),
    },
)

# Performs a subset diff between an actual (the subset) and
# an expected (superset) json files.
def _subset_diff_impl(ctx):
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = "python {sdiff_py} {expected} {actual}".format(
            sdiff_py = ctx.file._sdiff_py.short_path,
            expected = ctx.file.expected.short_path,
            actual = ctx.file.actual.short_path,
        ),
    )

    runfiles = [ctx.file._sdiff_py, ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles),
    )

subset_diff_test = rule(
    doc = """
        Computes a smart subset diff between two JSON objects.

        A subset diff is defined as follows:
        1. We allow every sub-dict in the expected file to contain additional
        keys that the actual file does not contain, but not the other way
        around. This should hold recursively.
        2. For leaf fields present in both files, that are primitive types
        (e.g. strings or numbers), their values must be equal.
        3. Corresponding lists must have the same number of elements (no
        sublists), and corresponding elements (index-wise) must satisify the
        subset relation.
        4. Finally, null/undefined values in the expected files are accepted
        to be equal to default values in actual of their respective types
        (e.g. "", []).

        Rational:
        1. Our protobuf definitions being tested here are incomplete: we
           intentionally ignore certain fields that are not useful to our tool.
           This means that in many cases, actual != expected.
        2. This behavior is not exhibited with lists: either protobuf parses
           the entire list when its part of the definition, or ignores it
           completely if it is not defined.
        3. Any null values in the expected json is parsed by protobuf as a
           default value of the corresponding type (e.g. 0 for ints). Our
           tool can either find out that the default value is a placeholder
           for null using the context, or does not exhibit a semnatic difference
           between null and the default value for the particular field.

        This rule takes a single argument: input.
        This is the json input file, or a rule that produces this json input
        file. The rule passes this input file in to the compiled
        p4_symbolic/main.cc which parses it with protobuf and then dumps it
        back to JSON.

        The rule checks that the dumped output (called actual) is a proper
        subset of the input (called exact).
        """,
    implementation = _subset_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = "The dumped protobuf JSON file, or a rule producing it.",
            mandatory = True,
            allow_single_file = True,
        ),
        "expected": attr.label(
            doc = """
                The original input json file (produced by p4c), or a
                rule producing it.
                """,
            mandatory = True,
            allow_single_file = True,
        ),
        "_sdiff_py": attr.label(
            doc = "The diff python script file.",
            mandatory = False,
            allow_single_file = True,
            default = "test_sdiff.py",
        ),
    },
)

# Macro that defines subset and exact diff rules for a given p4 program
# with all their dependent rules.
# The macro defines these exact rules, in this logical order of dependencies:
# 1. A rule for producing bmv2 json from a .p4 program using p4c.
# 2. A rule for parsing the bmv2 json using p4_symbolic/main.cc, and dumping
#    a protobuf and json output files, and an extraction rule for each
#    output file.
# 3. A rule for golden file testing of the protobuf output file against
#    the specified expected file.
# 4. A rule for subset diff testing of json output file (subset) against
#    the output of p4c (superset).
# 5. A test suite combining both 4 and 5.
# Use the p4_deps list to specify dependent files that p4_program input
# file depends on (e.g. by including them).
def bmv2_protobuf_parsing_test(name, p4_program, golden_file, p4_deps = []):
    p4c_name = "%s_p4c" % name
    parse_name = "%s_parse" % name
    exact_diff_name = "%s_exact_test" % name
    subset_diff_name = "%s_subset_test" % name

    # Run p4c to get bmv2 input .json file.
    run_p4c(
        name = p4c_name,
        src = p4_program,
        deps = p4_deps,
    )

    # Use p4_symbolic/main.cc to parse input json and dump
    # (tmp) output .pb.txt and .json files.
    proto_filename = name + "_tmp.pb.txt"
    json_filename = name + "_tmp.json"
    native.genrule(
        name = parse_name,
        srcs = [":" + p4c_name],
        outs = [proto_filename, json_filename],
        tools = ["//p4_symbolic/bmv2:test"],
        cmd = """
            $(location //p4_symbolic/bmv2:test) $(OUTS) < $(SRCS)
            """,
    )

    # Subset diff test between output and input json files
    subset_diff_test(
        name = subset_diff_name,
        actual = json_filename,
        expected = ":" + p4c_name,
    )

    # Exact diff test between output and golden protobuf files.
    exact_diff_test(
        name = exact_diff_name,
        actual = proto_filename,
        expected = golden_file,
    )

    # Group tests into a test_suite with the given name.
    # This is just to make the provided name alias to something.
    native.test_suite(
        name = name,
        tests = [
            ":" + subset_diff_name,
            ":" + exact_diff_name,
        ],
    )
