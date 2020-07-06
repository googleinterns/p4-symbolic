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

// Contains functions used to symbolically analyze/interprate actions
// and their bodies.
// An action is represented as a boolean symbolic z3 expression over
// unconstrained symbolic parameters corresponding to its actual P4 parameters.

#ifndef P4_SYMBOLIC_SYMBOLIC_ACTION_H_
#define P4_SYMBOLIC_SYMBOLIC_ACTION_H_

#include <string>
#include <unordered_map>

#include "p4_pdpi/utils/status_utils.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/structs.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace action {

// The context of analyzing an action body is a mapping between
// variables and symbolic values in its scope.
struct ActionContext {
  std::string action_name;
  // Variable name to its corresponding symbolic expression.
  std::unordered_map<std::string, z3::expr> scope;
};

// Symbolically Analyzes the given program, generating z3 symbolic
// expressions and that are later solved to produce concerete packets.
pdpi::StatusOr<ActionSymbolicTrace> AnalyzeAction(
    const ir::Action &action, const SolverState &solver_state);

}  // namespace action
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_ACTION_H_
