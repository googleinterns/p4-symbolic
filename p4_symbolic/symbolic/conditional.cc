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

// Contains functions used to symbolically evaluate P4 conditionals and their
// branches.

#include "p4_symbolic/symbolic/conditional.h"

#include "p4_symbolic/symbolic/action.h"
#include "p4_symbolic/symbolic/typed.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic {
namespace symbolic {
namespace conditional {

gutil::StatusOr<control::SymbolicHeadersAndTrace> EvaluateConditional(
    const Dataplane data_plane, const ir::Conditional &conditional,
    const SymbolicHeaders &headers) {
  // Evaluate both branches.
  ASSIGN_OR_RETURN(
      control::SymbolicHeadersAndTrace if_branch,
      control::EvaluateControl(data_plane, conditional.if_branch(), headers));
  ASSIGN_OR_RETURN(
      control::SymbolicHeadersAndTrace else_branch,
      control::EvaluateControl(data_plane, conditional.else_branch(), headers));

  // Evaluate the condition.
  action::ActionContext fake_context = {conditional.name(), {}};
  ASSIGN_OR_RETURN(
      TypedExpr condition,
      action::EvaluateRValue(conditional.condition(), headers, &fake_context));

  // Now we have two headers and traces that need mergine.
  // We should merge in a way such that the value of a header or trace is
  // the one from the if branch if the condition is true, and the else branch
  // otherwise.
  return control::SymbolicHeadersAndTrace{
      util::MergeHeadersOnCondition(else_branch.headers, if_branch.headers,
                                    condition),
      util::MergeTracesOnCondition(else_branch.trace, if_branch.trace,
                                   condition)};
}

}  // namespace conditional
}  // namespace symbolic
}  // namespace p4_symbolic
