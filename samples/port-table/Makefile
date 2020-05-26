SHELL := /bin/bash

run: build simple_switch control_plane packets

build: table.json

stop: kill clean

#
# Compiling
#
table.json: table.p4
	p4c --std p4_16 --target bmv2 --arch v1model table.p4

#
# bmv2 simulation
# run the simple_switch simulator on compiled program
# store process id for later killing
#
simple_switch: table.json veth switch.pid

switch.pid:
	@echo "simple switch logs available at switch.log"
	@{ sudo simple_switch --interface 0@veth0 --interface 1@veth2 table.json > switch.log & echo $$! > switch.pid; }
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
define port_exact =
table_add ports_exact set_egress_spec 0 => 1\n\
table_add ports_exact set_egress_spec 1 => 0\n\
table_dump ipv4_lpm
endef

control_plane: switch.pid
	@echo "simple_switch_CLI logs available at cli.log"
	@simple_switch_CLI <<< $$'$(port_exact)' > cli.log

#
# Sending Test Packets
#
define PACKETS =
p = Ether()/IP(dst="20.20.0.1")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.2")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.3")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.4")/UDP()\n\
sendp(p, iface="veth1")\n\
# this will show up once, if the program was incorrect, it would show up twice \n\
q = Ether()/IP(dst="20.20.0.8")/UDP()\n\
sendp(q, iface="veth3")\n
endef

packets.pid:
	@sudo tcpdump -n -i veth3 & echo $$! > packets.pid

packets: packets.pid
	@sudo scapy <<< $$'$(PACKETS)' > /dev/null

clean:
	@rm -f *.json *.p4i *.log

.PHONY: build run stop simple_switch veth control_plane packets kill clean
