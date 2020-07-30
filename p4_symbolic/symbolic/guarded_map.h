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

// Defines our GuardedMap class.

#ifndef P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_
#define P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_

#include <string>
#include <unordered_map>

#include "absl/status/status.h"
#include "google/protobuf/map.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// The GuardedMap class wraps around an internal std::unordered_map instance,
// while enforcing the following:
// 1. The GuardedMap class can only be instantiated with an instance of the IR
//    header definitions. The resulting GuardedMap instance will be initialized
//    to have exactly the same keys as the fields defined in those header
//    definitions. These keys are initially mapped to free symbolic variables,
//    with the same sort (including bitsize) described in the definitions.
// 2. The GuardedMap class is not copyable or movable, it can only be passed by
//    pointer or reference.
// 4. The GuardedMap class supports a const reference .get(<key>), which returns
//    an absl error if the key is not found in the map.
// 5. The GuardedMap class allows mutation via .set(<key>, <value>, <guard>),
//    which sets the value of the key to z3::ite(<guard>, <value>, <old value>),
//    after checking that the sort of <value> matches the sort of <old value>
//    modulo padding.
//
// As such, this class provides the following safety properties:
// 1. Once initialized, the class has a fixed set of keys.
// 2. A value mapped by a key allows has the same sort.
// 3. A value can only be assigned to a key given a guard.
//
class GuardedMap {
 private:
  // The underlying map storing the keys and their values.
  std::unordered_map<std::string, z3::expr> map_;
  absl::Status status_;

  // Private empty constructor.
  GuardedMap() {}

 public:
  // Constructor requires passing the headers definition and will fill the map
  // with a free symbolic variable per header field.
  explicit GuardedMap(
      const google::protobuf::Map<std::string, ir::HeaderType> &headers);

  // Accessors
  absl::Status status() { return this->status_; }

  // Only explicitly copyable!
  GuardedMap(const GuardedMap &other) = default;

  // Not movable, not assignable.
  GuardedMap(GuardedMap &&other) = delete;
  GuardedMap &operator=(const GuardedMap &other) = delete;
  GuardedMap &operator=(GuardedMap &&other) = delete;

  // Getters.
  size_t Count(const std::string &key) const;
  gutil::StatusOr<z3::expr> Get(const std::string &key) const;

  // Guarded setter.
  // Returns an error if the assigned value has incompatible sort with the
  // pre-defined value.
  absl::Status Set(const std::string &key, const z3::expr &value,
                   const z3::expr &guard);

  // Constant iterators.
  using const_iterator =
      std::unordered_map<std::string, z3::expr>::const_iterator;
  const_iterator begin() const noexcept { return this->map_.cbegin(); }
  const_iterator end() const noexcept { return this->map_.cend(); }
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_GUARDED_MAP_H_
