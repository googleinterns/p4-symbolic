load("@rules_cc//cc:defs.bzl", "cc_binary")

cc_binary(
    name = "main",
    srcs = ["src/main.cc"],
    deps = [
        "//src/protobuf:test_cc_proto",
        "@com_google_absl//absl/strings"
    ]
)
