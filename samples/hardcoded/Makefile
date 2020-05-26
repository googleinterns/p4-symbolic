SHELL := /bin/bash

run: build simple_switch packets

build: hardcoded.json

stop: kill clean

#
# Compiling
#
hardcoded.json: hardcoded.p4
	p4c --std p4_16 --target bmv2 --arch v1model hardcoded.p4

#
# bmv2 simulation
# run the simple_switch simulator on compiled program
# store process id for later killing
#
simple_switch: hardcoded.json veth switch.pid

switch.pid:
	@echo "simple switch logs available at switch.log"
	@{ sudo simple_switch --interface 0@veth0 --interface 1@veth2 hardcoded.json > switch.log & echo $$! > switch.pid; }
	@sleep 5

# create virtual ethernet interfaces
veth:
	@sudo ../veth_setup.sh > /dev/null

# kill running simple_switch
kill:
	@sudo kill `cat switch.pid` && sudo rm switch.pid
	@sudo kill `cat packets.pid` && rm packets.pid

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

.PHONY: build run stop simple_switch veth kill clean packets
