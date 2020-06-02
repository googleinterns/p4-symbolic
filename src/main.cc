#include <iostream>
#include <string>

// #include "absl/strings/str_cat.h"
// #include "absl/strings/string_view.h"
#include "google/protobuf/util/json_util.h"

#include "src/protobuf/bmv2/program.pb.h"

void ReadStdin(std::string& str) {
  std::istreambuf_iterator<char> cin_iterator{std::cin};
  std::istreambuf_iterator<char> end;
  str = std::string(cin_iterator, end);
}

int main() {
  // verify link and compile versions are the same
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  
  std::string input;
  ReadStdin(input);

  // testing absl
  // std::cout << absl::StrCat("Hello ", "World!") << std::endl;

  // parsing JSON
  P4Program program;
  google::protobuf::util::JsonParseOptions parsing_options;
  parsing_options.ignore_unknown_fields = true;
  google::protobuf::util::JsonStringToMessage(input, &program, parsing_options);

  // printing JSON
  google::protobuf::util::JsonPrintOptions dumping_options;
  dumping_options.add_whitespace = true;
  dumping_options.always_print_primitive_fields = true;
  dumping_options.preserve_proto_field_names = true;
  
  std::string output;
  google::protobuf::util::MessageToJsonString(program, &output, dumping_options);
  std::cout << output << std::endl;

  return 0;
};
