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

# This file defines a rule for running p4c and producing bmv2 json files.

def _run_p4c_impl(ctx):
    # Figure out the outpt file extension.
    # If provided explicitly, use that.
    # Otherwise, if the target is bmv2, the extension must be .json
    extension = ctx.attr.extension
    if extension == "":
        # Add other extensions here as needed.
        if ctx.attr.target == "bmv2":
            extension = ".json"
        else:
            fail("Extension is not provided for unknown target %s"
                % ctx.attr.target)

    # The output file path (relative to the directory of the src input file).
    fname = "".join([
        ctx.attr.name,
        "-bazel-p4c-tmp-output/",
        # Base name without the .p4 extension.
        ctx.file.src.basename[:-3],
        extension
    ])

    # Declare the output file.
    output_file = ctx.actions.declare_file(
        fname,
        sibling=ctx.file.src)

    # Get the full path (relative to root of sandbox) of the directory of
    # the output file.
    # This is needed because p4c expects a directory to be passed with "-o".
    # P4c will put the output file in that directory.
    output_dir_path = output_file.path[:-len(output_file.basename)-1]

    # Run p4c.
    ctx.actions.run_shell(
        inputs = [ctx.file.src] + ctx.files.deps,
        outputs = [output_file],
        use_default_shell_env = True,
        command = "p4c --std $1 --target $2 --arch $3 -o $4 $5 $6",
        arguments = [
            ctx.attr.std,
            ctx.attr.target,
            ctx.attr.arch,
            output_dir_path,
            ctx.attr.p4c_args,
            ctx.file.src.path
        ]
    )

    return [DefaultInfo(files = depset([output_file]))]

run_p4c = rule(
    doc = "Runs p4c to produce output files according to given params.",
    implementation = _run_p4c_impl,
    attrs = {
        "src": attr.label(
            doc = "Input .p4 files to pass to p4c.",
            mandatory = True,
            allow_single_file = [".p4"]
        ),
        "deps": attr.label_list(
            doc = "Other dependent files/labels. Use for included p4 files.",
            mandatory = False,
            allow_empty = True,
            allow_files = [".p4"],
            default = []
        ),
        "target": attr.string(
            doc = "The --target argument passed to p4c (default: bmv2).",
            mandatory = False,
            default = "bmv2"
        ),
        "arch": attr.string(
            doc = "The --arch argument passed to p4v (default: v1model).",
            mandatory = False,
            default = "v1model"
        ),
        "std": attr.string(
            doc = "The --std argument passed to p4v (default: p4_16).",
            mandatory = False,
            default = "p4_16"
        ),
        "p4c_args": attr.string(
            doc = "Any additional command line arguments to pass to p4c.",
            mandatory = False,
            default = ""
        ),
        "extension": attr.string(
            doc = """
                The expected extension of the ouput file, depending on
                the architecture.
                If the extension is not provided, the rule will attempt to
                figure this out by looking at the target attribute, and will
                throw an Error if it was not able to determine it.
                """,
            mandatory = False,
            default = ""
        )
    },
)
