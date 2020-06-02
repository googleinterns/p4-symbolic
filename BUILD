load("@rules_cc//cc:defs.bzl", "cc_binary")

cc_binary(
    name = "main",
    srcs = ["src/main.cc"],
    deps = [
        "//src/protobuf:p4_test_cc_proto",
        "@com_google_absl//absl/strings"
    ]
)
