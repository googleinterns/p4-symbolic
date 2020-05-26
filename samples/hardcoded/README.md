# Hard Coded 2-Ports Forwarding Switch

This is a simple P4 program that implements a switch with two ports: 0 and 1.

All traffic received via port 0 is then sent out to port 1 without modification, and vice-versa.

You can find additional explination about this particular program, as well as the p4 language
in this youtube tutorial https://www.youtube.com/watch?v=qxT7DKOIk7Q&t=3151s

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

When you are done experimenting, use `make stop` to remove all temporary files, shutdown simple_switch and tcpdump, and clean.

## Dependencies

You need to have `p4c`, `bmv2`, and `scapy` installed.
