#include <iostream>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/util/json_util.h"

#include "src/protobuf/test.pb.h"

int main() {
  // verify link and compile versions are the same
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  // testing absl
  std::cout << absl::StrCat("Hello ", "World!") << std::endl;

  TestMessage test_message;
  test_message.set_value(10);
  test_message.set_name("My String");

  // as a string
  std::cout << "String debug:" << std::endl;
  std::cout << test_message.DebugString() << std::endl;

  // as JSON
  std::string json_output;
  google::protobuf::util::MessageToJsonString(test_message, &json_output);
  std::cout << "JSON:" << std::endl;
  std::cout << json_output << std::endl << std::endl;

  // parsing JSON
  TestMessage test_message_2;
  google::protobuf::util::JsonStringToMessage(
      "{\"value\":1, \"name\": \"Testing\" }",
      &test_message_2);
  std::cout << "Debug Reading:" << std::endl;
  std::cout << test_message_2.DebugString() << std::endl;

  return 0;
};
