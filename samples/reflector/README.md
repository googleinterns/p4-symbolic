# Reflector Switch 

This is a simple P4 program that implements a reflector switch with two ports: 0 and 1.

All traffic received via a port is reflected back onto that same port.

## Running

You can build and run the various stages of the simulation of this program using
```
make
```

Internally, this first compiles the program
```
make build
```

Then, it runs bmv2's simple\_switch simulator on that program with virtual ethernet interfaces that the script creates
```
make simple_switch
```

Finally, the command monitors the output messages sent on port 1, and logs them via the screen, using `tcpdump`, it
also uses `scapy` to send test packets.

Every packet sent via port 1 (veth2<->veth3) will appear twice in the tcpdump output, the first appearance is logged
when scapy sends the packet initially, and the second is logged when the switch reflects it back.

When you are done experimenting, use `make stop` to remove all temporary files, shutdown simple_switch and tcpdump, and clean.

## Dependencies

You need to have `p4c`, `bmv2`, and `scapy` installed.
