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

#ifndef P4_SYMBOLIC_IR_PDPI_DRIVER_H_
#define P4_SYMBOLIC_IR_PDPI_DRIVER_H_

#include <string>

#include "absl/status/status.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/utils/status_utils.h"

namespace p4_symbolic {
namespace ir {

// Parses the p4info file given by "p4info_path" into a pdpi:IrP4Info
// instance.
// Returns the parsed IrP4Info instance, or an appropriate failure status
// in case of a badly formatted input file, or if the file does not exist.
pdpi::StatusOr<pdpi::ir::IrP4Info> ParseP4InfoFile(std::string p4info_path);

}  // namespace ir
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_IR_PDPI_DRIVER_H_
