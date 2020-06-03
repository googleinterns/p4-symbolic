load("//testing:bmv2_parsing_check.bzl", "subset_diff_test")
load("//:p4c.bzl", "run_p4c")

test_suite(
    name = "parsing",
    tests = [
      ":port_table_test",
      ":hardcoded_test",
      ":reflector_test",
      ":ipv4_test"
    ]
)

# subset diff tests that check
# dumped parsed json is a subset of p4c output json
subset_diff_test(
    name = "port_table_test",
    input = ":p4c_table"
)

subset_diff_test(
    name = "hardcoded_test",
    input = ":p4c_hardcoded"
)

subset_diff_test(
    name = "reflector_test",
    input = ":p4c_reflector"
)

subset_diff_test(
    name = "ipv4_test",
    input = ":p4c_ipv4"
)

# rules for compiling p4 programs to bmv2 json files
run_p4c(
  name = "p4c_table",
  p4program = "samples/port-table/table.p4"
)

run_p4c(
  name = "p4c_hardcoded",
  p4program = "samples/hardcoded/hardcoded.p4"
)

run_p4c(
  name = "p4c_reflector",
  p4program = "samples/reflector/reflector.p4"
)

run_p4c(
  name = "p4c_ipv4",
  p4program = "samples/ipv4-routing/basic.p4"
)
