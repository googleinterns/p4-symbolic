SHELL := /bin/bash

run: build simple_switch control_plane packets.pid

build: basic.json

stop: kill clean

#
# Compiling
#
basic.json: basic.p4
	p4c --std p4_16 --target bmv2 --arch v1model basic.p4

#
# bmv2 simulation
# run the simple_switch simulator on compiled program
# store process id for later killing
#
simple_switch: basic.json veth switch.pid

switch.pid:
	@echo "simple switch logs available at switch.log"
	@{ sudo simple_switch --interface 0@veth0 --interface 1@veth2 basic.json > switch.log & echo $$! > switch.pid; }
	@sleep 5

# create virtual ethernet interfaces
veth:
	@sudo ../veth_setup.sh > /dev/null

# kill running simple_switch
kill:
	@sudo kill `cat switch.pid` && sudo rm switch.pid
	@sudo kill `cat packets.pid` && rm packets.pid

#
# Control Plane
# insert entries into p4 tables
#
define ipv4_lpm =
table_add ipv4_lpm ipv4_forward 10.10.0.0/16 => 00:00:00:00:00:00 0\n\
table_add ipv4_lpm ipv4_forward 20.20.0.0/16 => 22:00:00:00:00:22 1\n\
table_dump ipv4_lpm
endef

control_plane: switch.pid
	@echo "simple_switch_CLI logs available at cli.log"
	@simple_switch_CLI <<< $$'$(ipv4_lpm)' > cli.log

#
# Sending Test Packets
#
define PACKETS =
p = Ether()/IP(dst="20.20.0.1")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.2")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="10.10.0.1")/UDP()\n\
sendp(p, iface="veth1")\n # wont show
endef

packets.pid:
	@sudo tcpdump -n -i veth3 & echo $$! > packets.pid
	@sudo scapy <<< $$'$(PACKETS)' > /dev/null

clean:
	@rm -f *.json *.p4i *.log

.PHONY: build run stop simple_switch veth kill control_plane clean
