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

#include "p4_symbolic/ir/pdpi_driver.h"

#include <memory>

#include "p4_pdpi/util.h"

namespace p4_symbolic {
namespace ir {

pdpi::StatusOr<pdpi::ir::IrP4Info> ParseP4InfoFile(
    const std::string &p4info_path) {
  p4::config::v1::P4Info p4info;
  RETURN_IF_ERROR(pdpi::ReadProtoFromFile(p4info_path.c_str(), &p4info));

  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4InfoManager> & info_manager,
                   pdpi::P4InfoManager::Create(p4info));

  return info_manager->GetIrP4Info();
}

}  // namespace ir
}  // namespace p4_symbolic
