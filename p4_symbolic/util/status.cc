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

#include "p4_symbolic/util/status.h"

namespace p4_symbolic {
namespace util {

namespace pb_err = google::protobuf::util::error;

absl::Status ProtobufToAbslStatus(
    const google::protobuf::util::Status& status) {
  absl::StatusCode out_code;

  google::protobuf::util::error::Code code = status.code();
  switch (code) {
    case pb_err::OK:
      out_code = absl::StatusCode::kOk;
      break;
    case pb_err::CANCELLED:
      out_code = absl::StatusCode::kCancelled;
      break;
    case pb_err::UNKNOWN:
      out_code = absl::StatusCode::kUnknown;
      break;
    case pb_err::INVALID_ARGUMENT:
      out_code = absl::StatusCode::kInvalidArgument;
      break;
    case pb_err::DEADLINE_EXCEEDED:
      out_code = absl::StatusCode::kDeadlineExceeded;
      break;
    case pb_err::NOT_FOUND:
      out_code = absl::StatusCode::kNotFound;
      break;
    case pb_err::ALREADY_EXISTS:
      out_code = absl::StatusCode::kAlreadyExists;
      break;
    case pb_err::PERMISSION_DENIED:
      out_code = absl::StatusCode::kPermissionDenied;
      break;
    case pb_err::UNAUTHENTICATED:
      out_code = absl::StatusCode::kUnauthenticated;
      break;
    case pb_err::RESOURCE_EXHAUSTED:
      out_code = absl::StatusCode::kResourceExhausted;
      break;
    case pb_err::FAILED_PRECONDITION:
      out_code = absl::StatusCode::kFailedPrecondition;
      break;
    case pb_err::ABORTED:
      out_code = absl::StatusCode::kAborted;
      break;
    case pb_err::OUT_OF_RANGE:
      out_code = absl::StatusCode::kOutOfRange;
      break;
    case pb_err::UNIMPLEMENTED:
      out_code = absl::StatusCode::kUnimplemented;
      break;
    case pb_err::INTERNAL:
      out_code = absl::StatusCode::kInternal;
      break;
    case pb_err::UNAVAILABLE:
      out_code = absl::StatusCode::kUnavailable;
      break;
    case pb_err::DATA_LOSS:
      out_code = absl::StatusCode::kDataLoss;
      break;
    default:
      out_code = absl::StatusCode::kUnknown;
  }

  return absl::Status(out_code, status.error_message().ToString());
}

}  // namespace util
}  // namespace p4_symbolic
