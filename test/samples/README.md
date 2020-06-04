# P4 Sample Programs

This directory contains a collection of sample P4 programs with a simple testing environment.

1. Reflector: a simple switch that reflects back all received packets onto the port it received them form.
2. hardcoded: a simple switch with two ports, that forwards every packet received on one port to the other, implemented via a hardcoded if statement.
3. port-table: same as hardcoded, but implemented via a contorl plane table.
4. ipv4-routing: a switch that routes packets based on their destination ipv4 using an LPM table.


## Running

First `cd` into the directory of the sample you want to run you can then compile, simulate, and run the tests in one shot using
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

After that, it installs the control plane table entries into the switch's control tables using simple\_switch\_cli. Note that this is only
performed for programs that have control plane tables
```
make simple_switch_cli
```

Finally, the command monitors the output messages sent on port 1, and logs them via the screen, using `tcpdump`, it
also uses `scapy` to send test packets.

When you are done experimenting, use `make stop` to remove all temporary files, shutdown simple_switch and tcpdump, and clean.

## Dependencies

You need to have `p4c`, `bmv2`, and `scapy` installed.

# Credits

These resources were used either for inspiration or as learning materials for writing the p4 routing program and the testing architecture and packets.

- The p4 tutorials https://github.com/p4lang/tutorials and associated youtube videos https://www.youtube.com/watch?v=qxT7DKOIk7Q
- The p4app build and simulate system https://github.com/p4lang/p4app
- This very nice blogpost by Bruno Rijsman https://hikingandcoding.wordpress.com/2019/09/17/getting-started-with-p4/
