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
    A smart diff in this context is a super set diff: the expected file contains
    a superset of attributes. The diff checks that for the ones that do exist
    in the actual output, the same value is assigned in the expected file.
    Attributes appearing in the actual file but not in the expected file are
    rejected.
    Finally, this subset notion is recursive. It applies to JSON objects
    nested within other JSON objects.
    This rule takes a single argument: input. This is the json input file,
    or a rule that produces this json input file.
    The rule passes this input file in to src/main.cc which parses it with
    protobuf and then dumps it back to JSON.
    The rule checks that the dumped output is a proper subset of the input.
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
