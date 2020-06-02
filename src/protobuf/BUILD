# https://blog.bazel.build/2017/02/27/protocol-buffers.html

load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

cc_proto_library(
    name = "p4_test_cc_proto",
    deps = [":p4_test_proto"],
    visibility = ["//:__pkg__"]
)

proto_library(
    name = "p4_test_proto",
    srcs = [
      "bmv2/header.proto",
      "bmv2/parser.proto",
      "bmv2/primitives.proto",
      "bmv2/program.proto",
      "bmv2/table.proto"
    ],
    deps = [
      "@com_google_protobuf//:struct_proto",
    ]
)
