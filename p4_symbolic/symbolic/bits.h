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

// Contains functions for creating, manipulating, and evaluating symbolic bit
// strings.

#ifndef P4_SYMBOLIC_SYMBOLIC_BITS_H_
#define P4_SYMBOLIC_SYMBOLIC_BITS_H_

#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace bits {

// Create a symbolic vector of a given size.
z3::expr BitVector(const char *name, unsigned int bit_size);

}  // namespace bits
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_BITS_H_
