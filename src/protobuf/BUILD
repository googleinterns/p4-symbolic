# https://blog.bazel.build/2017/02/27/protocol-buffers.html

load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

cc_proto_library(
    name = "test_cc_proto",
    deps = [":test_proto"],
    visibility = ["//:__pkg__"]
)

proto_library(
    name = "test_proto",
    srcs = ["test.proto"]
)
