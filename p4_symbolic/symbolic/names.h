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

// Contain functions that extract consistent and unique SMT symbolic
// variable and function names from the corresponding P4Program entities.

#ifndef P4_SYMBOLIC_SYMBOLIC_NAMES_H_
#define P4_SYMBOLIC_SYMBOLIC_NAMES_H_

#include <string>

#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace symbolic {
namespace names {

// The name of the symbolic variable whose value
// corresponds to the value of the header field.
std::string ForHeaderField(const ir::HeaderType &header_type,
                           const ir::HeaderField &header_field);

// Name of the header field access by this HeaderValue expression.
// Consistent with ForHeaderField(...).
std::string ForHeaderField(const ir::FieldValue &field_value);

// The name of the symbolic predicate (boolean function)
// that represents the behavior of the corresponding action.
std::string ForAction(const ir::Action &action);

// The name of the symbolic variable whose value
// corresponds to the value of the action parameter.
std::string ForActionParameter(
    const ir::Action &action,
    const pdpi::ir::IrActionDefinition::IrActionParamDefinition &param);

// The name of the indicator symbolic variable whoose value corresponds
// to the given table entry being matched on.
std::string ForTableEntry(const std::string &table_name, int entry_index);

// The name of the indicator symbolic variable determining if the packet
// was dropped (e.g. did not match any entry in some table).
std::string ForDroppedPacket();

}  // namespace names
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_NAMES_H_
