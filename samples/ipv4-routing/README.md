# Basic IPv4 forwarding

This is a simple P4 program that implements basic IPv4 forwarding.

Taken from https://github.com/p4lang/tutorials basic tutorial.

It performs the following pipeline on every received packet:
* parse the packet and extract the ethernet and ipv4 headers
* lookup the mac address and out going port of the next hop from the control plane tables
* update packet headers with the new address and port and decrement ttl
* serialize (deparse) packet and send it via the new port

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

After that, it installs the control plane table entries into the switch's control tables using simple\_switch\_cli
```
make simple_switch_cli
```

Finally, the command monitors the output messages sent on port 1, and logs them via the screen, using `tcpdump`, it
also uses `scapy` to send test packets.

When you are done experimenting, use `make stop` to remove all temporary files, shutdown simple_switch and tcpdump, and clean.

## Dependencies

You need to have `p4c`, `bmv2`, and `scapy` installed.

## Test Architecture

The test follows a very simple network architecture.

The switch is connected to two ports: 0 and 1, with 4 virtual ethernet interfaces: veth0, veth1, veth2, and veth3.

veth0 and veth1 are piped togther, same with veth2 and veth3. Packets sent via veth0 appear as outputs on veth1 and vice-versa.

Finally, the switch assigns veth0 to port 0, and veth1 to port 1.

The control plane has two longest prefix rules: it routes all packets to 10.10.0.0/16 to port 0 (thus they appear at veth1) and all
packets to 20.20.0.0/16 to port 1 (thus they appear at veth3). Other packets are dropped.

The makefile sends 3 test packets: two to 20.20.0.1, and one to 10.10.0.1, using differnet ports. The makefile monitors packets
appearing at veth3 (the other end of port 1), and thus shows exactly two of these packets only.

# Credits

These resources were used either for inspiration or as learning materials for writing the p4 routing program and the testing architecture and packets.

- The p4 tutorials https://github.com/p4lang/tutorials
- The p4app build and simulate system https://github.com/p4lang/p4app
- This very nice blogpost by Bruno Rijsman https://hikingandcoding.wordpress.com/2019/09/17/getting-started-with-p4/
