#include <iostream>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

int main() {
    std::cout << absl::StrCat("Hello ", "Kinan!") << std::endl;
    return 0;
}
