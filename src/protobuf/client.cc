#include "test.pb.h"

#include <google/protobuf/util/json_util.h>

#include <iostream>
#include <stdio.h>

int main() {
    GOOGLE_PROTOBUF_VERIFY_VERSION; // verify link and compile versions are the same

    TestMessage test_message;
    test_message.set_value(10);
    test_message.set_name("Kinan");

    // as a string
    std::cout << "String debug:" << std::endl << test_message.DebugString() << std::endl;

    // as JSON
    std::string json_output;
    google::protobuf::util::MessageToJsonString(test_message, &json_output);
    std::cout << "JSON:" << std::endl << json_output << std::endl << std::endl;

    // parsing JSON
    TestMessage test_message_2;
    google::protobuf::util::JsonStringToMessage("{\"value\":1, \"name\": \"Testing\" }", &test_message_2);
    std::cout << "Debug Reading:" << std::endl << test_message_2.DebugString() << std::endl;

    return 0;
};
