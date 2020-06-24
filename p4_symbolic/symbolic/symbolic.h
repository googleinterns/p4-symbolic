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

#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic {
namespace symbolic {

class Analyzer {
 private:
 public:
  // Class is not copyable or movable.
  Analyzer(const Analyzer&) = delete;
  Analyzer& operator=(const Analyzer&) = delete;
  Analyzer(Analyzer&&) = delete;
  Analyzer& operator=(Analyzer&&) = delete;

  // Header related functions.
  void AnalyzeHeaderType(ir::HeaderType);
  void AnalyzeHeaderField(ir::HeaderField);

  // Table related functions.
  void AnalyzeTable(ir::Table);

  // Action, statements, and expressions.
  void AnalyzeAction(ir::Action);
  void AnalyzeStatement(ir::Statement);
  void AnalyzeAssignmentStatement(ir::AssignmentStatement);
  void AnalyzeLValue(ir::LValue);
  void AnalyzeRValue(ir::RValue);
  void AnalyzeFieldValue(ir::FieldValue);
  void AnalyzeVariable(ir::Variable);

  // Overal program.
  void AnalyzeProgram(ir::P4Program program);
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_IR_PDPI_DRIVER_H_
