def _subset_diff_impl(ctx):
    # diff expected with tmp file
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = "{binary} < {expected} | python {py_file} {expected}".format(
            py_file = ctx.file.py_file.short_path,
            binary = ctx.file.actual.short_path,
            expected = ctx.file.expected.short_path
        )
    )

    runfiles = [ctx.file.py_file, ctx.file.actual, ctx.file.expected]
    return DefaultInfo(
        runfiles = ctx.runfiles(files = runfiles),
    )

subset_diff_test = rule(
    doc = """Computes a smart subset diff of two JSON files, checking that they agree.
    A smart diff in this context is a super set diff: the expected file contains
    a superset of attributes. The diff checks that for the ones that do exist
    in the actual output, the same value is assigned in the expected file.
    Attributes appearing in the actual file but not in the expected file are
    rejected.
    Finally, this subset notion is recursive. It applies to JSON objects
    nested within other JSON objects.
    """,
    implementation = _subset_diff_impl,
    test = True,
    attrs = {
        "actual": attr.label(
            doc = "'Actual' file, typically containing the output of some command.",
            mandatory = True,
            allow_single_file = True,
        ),
        "expected": attr.label(
            doc = """Expected file.""",
            mandatory = True,
            allow_single_file = True,
        ),
        "py_file": attr.label(
            doc = """The diff python script file. 
                     Do not override this unless you know what you are doing.""",
            mandatory = False,
            allow_single_file = True,
            default = "sdiff.py"
        )
    },
)
