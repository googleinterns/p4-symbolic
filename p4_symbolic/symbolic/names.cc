// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "p4_symbolic/symbolic/names.h"

#include "absl/strings/str_format.h"

namespace p4_symbolic {
namespace symbolic {
namespace names {

std::string ForHeaderField(const ir::HeaderType &header_type,
                           const ir::HeaderField &header_field) {
  return absl::StrFormat("%s.%s", header_type.name(), header_field.name());
}

std::string ForHeaderField(const ir::FieldValue &field_value) {
  return absl::StrFormat("%s.%s", field_value.header_name(),
                         field_value.field_name());
}

std::string ForAction(const ir::Action &action) {
  return action.action_definition().preamble().name();
}

std::string ForActionParameter(
    const ir::Action &action,
    const pdpi::ir::IrActionDefinition::IrActionParamDefinition &param) {
  return absl::StrFormat("%s.%s", ForAction(action), param.param().name());
}

std::string ForTableEntry(const std::string &table_name, int entry_index) {
  return absl::StrFormat("%s.%d", table_name, entry_index);
}

std::string ForDroppedPacket() { return "__dropped__"; }

}  // namespace names
}  // namespace symbolic
}  // namespace p4_symbolic
