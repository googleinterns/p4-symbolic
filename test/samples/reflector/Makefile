# Copyright 2020 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

SHELL := /bin/bash

run: build simple_switch packets

#
# Sending Test Packets
#
define PACKETS =
# These wont show up \n\
p = Ether()/IP(dst="20.20.0.1")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.2")/UDP()\n\
sendp(p, iface="veth1")\n\
# These will show up twice each \n\
p = Ether()/IP(dst="20.20.0.3")/UDP()\n\
sendp(p, iface="veth3")\n\
p = Ether()/IP(dst="20.20.0.4")/UDP()\n\
sendp(p, iface="veth3")\n\
q = Ether()/IP(dst="20.20.0.8")/UDP()\n\
sendp(q, iface="veth3")\n
endef

# include main Makefile with rules
include ../Makefile
