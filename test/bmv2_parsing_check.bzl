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

def _parse_bmv2_impl(ctx):
    # come up with a base name in a tmp directory
    # for the .json and .pb.txt output files
    basename = "".join([
        ctx.attr.name,
        "-parse-bmv2-tmp/",
        ctx.file.input.basename[:-3]
    ])

    # declare output files
    protobuf = ctx.actions.declare_file(
        basename + ".pb.txt",
        sibling=ctx.file.input
    )
    json = ctx.actions.declare_file(
        basename + ".json",
        sibling=ctx.file.input
    )

    # run the compiled binary to produce outputs
    ctx.actions.run_shell(
        inputs = [ctx.file._main, ctx.file.input],
        outputs = [protobuf, json],
        use_default_shell_env = True,
        command = "{binary} {protobuf} {json} < {input}".format(
            binary = ctx.file._main.path,
            protobuf = protobuf.path,
            json = json.path,
            input = ctx.file.input.path
        )
    )

    # return all outputs by default
    # as well as a single output group per json and protobuf
    return [
        DefaultInfo(
            files = depset([protobuf, json]),
            runfiles = ctx.runfiles(files = [ctx.file.input, ctx.file._main])
        ),
        OutputGroupInfo(
            json = depset([json]),
            protobuf = depset([protobuf])
        )
    ]

parse_bmv2 = rule(
    doc = """"Runs our protobuf-based parsing binary on
              an input bmv2 json (or a rule producing it),
              and outputs a protobuf and json dump files.""",
    implementation = _parse_bmv2_impl,
    attrs = {
        "input": attr.label(
            doc = "Input json bmv2 program to feed to our parsing binary.",
            mandatory = True,
            allow_single_file = True
        ),
        "_main": attr.label(
            doc = "src/main.cc binary that parses with protobuf.",
            mandatory = False,
            allow_single_file = True,
            default = "//:main"
        )
    }
)

def _extract_output_group_impl(ctx):
    output_group_name = ctx.attr.output_group
    output_group = ctx.attr.target[OutputGroupInfo][output_group_name]
    return [DefaultInfo(files = output_group)]

extract_output_group = rule(
    doc = """Extract the specified output group from a provided target..
             Always targets to depend on the specified output group only,
             instead of the entire dependent target.""",
    implementation = _extract_output_group_impl,
    attrs = {
        "target": attr.label(
            doc = "The target to extract outputs from.",
            mandatory = True,
            allow_files = False,
            providers = [[OutputGroupInfo]]
        ),
        "output_group": attr.string(
            doc = "The name of the output group to extract.",
            mandatory = True
        )
    }
)

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
                echo "Please run \"bazel run //{package}:{name} -- --update" first."
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
            name = ctx.label.name
        )
    )

    runfiles = [ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles)
    )

exact_diff_test = rule(
    doc = """Computes diff of two files, fails if they disagree.

    Takes two attributes that represent the files to compare, or rules
    producing them.
    """,
    implementation = _exact_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = """The 'Actual' file.
                     Typically the output of some command.
                     This is not checked in and is only temporary.""",
            mandatory = True,
            allow_single_file = True,
        ),
        "expected": attr.label(
            doc = """Expected file (aka golden file),.
                     Typically an actual file that is checked in.""",
            mandatory = True,
            allow_single_file = True,
        )
    }
)

def _subset_diff_impl(ctx):
    # diff expected with tmp file
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = "python {py_file} {expected} {actual}".format(
            py_file = ctx.file._py_file.short_path,
            expected = ctx.file.expected.short_path,
            actual = ctx.file.actual.short_path
        )
    )

    runfiles = [ctx.file._py_file, ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles)
    )

subset_diff_test = rule(
    doc = """Computes a smart subset diff between two JSON objects.

    A subset diff is defined as follows:
    1. We allow every sub-dict in the expected file to contain additional keys
    that the actual file does not contain, but not the other way around.
    This should hold recursively.
    2. For leaf fields present in both files, that are primitive types
    (e.g. strings or numbers), their values must be equal.
    3. Corresponding lists must have the same number of elements (no sublists),
    and corresponding elements (index-wise) must satisify the subset relation.
    4. Finally, null/undefined values in the expected files are accepted to be
    equal to default values in actual of their respective types (e.g. "", []).

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
    This is the json input file, or a rule that produces this json input file.
    The rule passes this input file in to the compiled src/main.cc which parses
    it with protobuf and then dumps it back to JSON.

    The rule checks that the dumped output (called actual) is a proper subset
    of the input (called exact).
    """,
    implementation = _subset_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = "The dumped protobuf JSON file, or a rule producing it.",
            mandatory = True,
            allow_single_file = True
        ),
        "expected": attr.label(
            doc = """The original input json file (produced by p4c), or a
                  rule producing it.""",
            mandatory = True,
            allow_single_file = True
        ),
        "_py_file": attr.label(
            doc = "The diff python script file.",
            mandatory = False,
            allow_single_file = True,
            default = "sdiff.py"
        )
    }
)
