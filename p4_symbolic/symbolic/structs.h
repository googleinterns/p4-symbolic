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

// Contains structs used by our symbolic analysis.

#ifndef P4_SYMBOLIC_SYMBOLIC_STRUCTS_H_
#define P4_SYMBOLIC_SYMBOLIC_STRUCTS_H_

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "google/protobuf/repeated_field.h"
#include "p4_pdpi/utils/status_utils.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// The result of analyzing an action and its body.
// It encapsulates a symbolic expression expressing its body's behavior in
// terms of its symbolic parameters.
// It provides a way to instantiate these parameters (and thus the body) for
// given concrete values.
class ActionSymbolicTrace {
 protected:
  // The fully qualified name of the corresponding action.
  std::string action_name_;
  // Z3 symbolic expressions (essentially symbolic variables) corresponding
  // to each parameter the action takes in order of declaration.
  std::vector<z3::expr> parameters_;
  // Symbolic expression expressing the semantic meaning of the action body,
  // over the symbolic parameters.
  z3::expr body_;

 public:
  ActionSymbolicTrace(std::string action_name, std::vector<z3::expr> parameters,
                      z3::expr body)
      : action_name_(action_name), parameters_(parameters), body_(body) {}

  // Instantiate the symbolic body defined over symbolic parameters with the
  // given values for these parameters.
  pdpi::StatusOr<z3::expr> instantiate(
      const google::protobuf::RepeatedField<int> &values) const {
    if (((unsigned int)values.size()) != this->parameters_.size()) {
      return absl::Status(
          absl::StatusCode::kInvalidArgument,
          absl::StrCat("Match entry has inconsistent number of parameters"));
    }

    z3::expr instantiated_call = this->body_;
    for (size_t i = 0; i < this->parameters_.size(); i++) {
      instantiated_call =
          instantiated_call && (this->parameters_.at(i) == values.at(i));
    }

    return instantiated_call;
  }
};

// The overall state of our symbolic analysis.
// This is returned by our main analysis function, and is used
// to find concrete test packets and for debugging.
struct SolverState {
  // The IR represnetation of the p4 program being analyzed.
  ir::P4Program program;
  // Z3 context wrapped in a smart pointer.
  // z3::context implements a private copy constructor and no move contructor.
  // This makes the call tostd::move(<context>) in pdpi::StatusOr
  // fail with a compile time error.
  // Z3's context is not meant to be copied or moved, related symbolic
  // expressions must be created using the exact same context.
  // Using a smart pointer address these issues and automatically manages the
  // memory.
  std::unique_ptr<z3::context> context;
  // Maps fully qualified action name to its symbolic trace, which can be used
  // to instatiate it for concrete parameter values.
  std::unordered_map<std::string, ActionSymbolicTrace> action_map;
  // Similar issue to context make unique_ptr desirable here.
  // Defining the solver here and re-using it for all future analysis allows
  // Z3 to remember interesting judgments it made about our trace constraints,
  // and also avoid storing and handling z3 symbolic constraints directly.
  std::unique_ptr<z3::solver> solver;
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_STRUCTS_H_
