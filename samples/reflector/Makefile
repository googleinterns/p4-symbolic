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
