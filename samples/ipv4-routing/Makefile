SHELL := /bin/bash

run: build simple_switch control_plane packets

#
# Control Plane
# insert entries into p4 tables
#
define CONTROL_PLANE_COMMANDS =
table_add ipv4_lpm ipv4_forward 10.10.0.0/16 => 00:00:00:00:00:00 0\n\
table_add ipv4_lpm ipv4_forward 20.20.0.0/16 => 22:00:00:00:00:22 1\n\
table_dump ipv4_lpm
endef

#
# Sending Test Packets
#
define PACKETS =
p = Ether()/IP(dst="20.20.0.1")/UDP()\n\
sendp(p, iface="veth1")\n\
p = Ether()/IP(dst="20.20.0.2")/UDP()\n\
sendp(p, iface="veth1")\n\
# this should show up once \n\
p = Ether()/IP(dst="10.10.0.1")/UDP()\n\
sendp(p, iface="veth3")\n\
# this should not show up \n\
p = Ether()/IP(dst="10.10.0.2")/UDP()\n\
sendp(p, iface="veth1")\n
endef

# include main Makefile with rules
include ../Makefile
