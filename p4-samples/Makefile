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

# Files that store various logs
SIMPLE_SWITCH_LOG := switch.log
SIMPLE_SWITCH_CLI_LOG := cli.log

# Files that store running process id for clean stop later
SIMPLE_SWITCH_PID := switch.pid
TCPDUMP_PID := packets.pid

# All compiled file names
SOURCE_FILE_NAMES := $(wildcard *.p4)
COMPILED_FILE_NAMES := $(SOURCE_FILE_NAMES:.p4=.json)

#
# Compiling
#
build: $(COMPILED_FILE_NAMES)

%.json: %.p4
	p4c --std p4_16 --target bmv2 --arch v1model --p4runtime-files $(basename $@).pb.txt $<

#
# bmv2 simulation
# run the simple_switch simulator on compiled program
# store process id for later killing
#
simple_switch: build veth $(SIMPLE_SWITCH_PID)

$(SIMPLE_SWITCH_PID):
	@echo "simple switch logs available at $(SIMPLE_SWITCH_LOG)"
	@{ sudo simple_switch --interface 0@veth0 --interface 1@veth2 $(COMPILED_FILE_NAMES) > $(SIMPLE_SWITCH_LOG) & echo $$! > $(SIMPLE_SWITCH_PID); }
	@sleep 5

veth:
	# create virtual ethernet interfaces
	@sudo ../veth_setup.sh $(VETH_PAIRS_COUNT) > /dev/null

#
# Control Plane
# insert entries into p4 tables
#
control_plane: $(SIMPLE_SWITCH_PID)
	@echo "simple_switch_CLI logs available at $(SIMPLE_SWITCH_CLI_LOG)"
	@simple_switch_CLI <<< $(CONTROL_PLANE_COMMANDS) > $(SIMPLE_SWITCH_CLI_LOG)

#
# Sending Test Packets
#
$(TCPDUMP_PID):
	@sudo tcpdump -n -i veth3 & echo $$! > $(TCPDUMP_PID)

packets: $(TCPDUMP_PID)
	@sudo scapy <<< $$'$(PACKETS)' > /dev/null

#
# Stopping all background processing and cleaning
#
stop: kill clean

kill:
	@sudo kill `cat $(SIMPLE_SWITCH_PID)` || echo "simple switch is not running!"
	@sudo rm -f $(SIMPLE_SWITCH_PID)
	@sudo kill `cat $(TCPDUMP_PID)` || echo "tcpdump is not running!"
	@sudo rm -f $(TCPDUMP_PID)

clean:
	@rm -f *.json *.p4i *.log *.info.* *.pb.txt

# PHONY rules with names that do not correspond to files
.PHONY: build simple_switch veth control_plane packets stop kill clean
