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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#ifndef P4_SYMBOLIC_SYMBOLIC_UTIL_H
#define P4_SYMBOLIC_SYMBOLIC_UTIL_H

#include "p4_symbolic/symbolic/symbolic.h"
#include "z3.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

SymbolicContext FreeSymbolicContext(z3::context *z3_context);

ConcreteContext ExtractFromModel(SymbolicContext context, z3::model model);

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
