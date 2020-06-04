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

def _run_p4c_impl(ctx):
    fname = "".join([
        ctx.attr.name,
        "-bazel-tmp-output/",
        ctx.file.p4program.basename[:-3],
        ".json"
    ])

    json_output_file = ctx.actions.declare_file(
        fname,
        sibling=ctx.file.p4program
    )

    out_dir = json_output_file.path[:-len(json_output_file.basename)-1]
    ctx.actions.run_shell(
        inputs = [ctx.file.p4program],
        outputs = [json_output_file],
        use_default_shell_env = True,
        command = "p4c --std p4_16 --target bmv2 --arch v1model -o $1 $2",
        arguments = [
            out_dir,
            ctx.file.p4program.path
        ]
    )

    return [DefaultInfo(files = depset([json_output_file]))]

run_p4c = rule(
    doc = "Runs p4c to produce output compiled files according to given params",
    implementation = _run_p4c_impl,
    attrs = {
        "p4program": attr.label(
            doc = "Input .p4 program to compile into a bmv2 JSON",
            mandatory = True,
            allow_single_file = True,
        )
    },
)
