load("//testing:bmv2_parsing_check.bzl", "subset_diff_test")

test_suite(
    name = "parsing",
    tests = [
      ":table_test",
      ":basic_test"
    ]
)

subset_diff_test(
    name = "table_test",
    actual = "//:main",
    expected = "testdata/table.json",
)

subset_diff_test(
    name = "basic_test",
    actual = "//:main",
    expected = "testdata/basic.json",
)
