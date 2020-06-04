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

def _subset_diff_impl(ctx):
    # diff expected with tmp file
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = "{binary} < {input} | python {py_file} {input}".format(
            py_file = ctx.file._py_file.short_path,
            binary = ctx.file._binary.short_path,
            input = ctx.file.input.short_path
        )
    )

    runfiles = [ctx.file._py_file, ctx.file._binary, ctx.file.input]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles),
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
        "input": attr.label(
            doc = "The input JSON file, or a rule producing it (typically invoking p4c)",
            mandatory = True,
            allow_single_file = True
        ),
        "_py_file": attr.label(
            doc = "The diff python script file.",
            mandatory = False,
            allow_single_file = True,
            default = "sdiff.py"
        ),
        "_binary": attr.label(
            doc = "src/main.cc binary that uses the protobuf definitions",
            mandatory = False,
            allow_single_file = True,
            default = "//:main"
        )
    }
)
