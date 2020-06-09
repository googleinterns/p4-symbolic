#!/bin/bash

count=$1

# The script must be run as root!
if [[ $(/usr/bin/id -u) -ne 0 ]]; then
    echo "Not running as root"
    exit
fi

# Create $count many pairs of virtual interfaced, each interface in a pair
# is hooked up to the other interface in that pair.
for i in $(seq 0 $(($count-1))); do
    # come up with unique names for two virtual ethernet interfaces
    in_veth="veth$(($i*2))"
    out_veth="veth$(($i*2+1))"

    if ! ip link show $in_veth &> /dev/null; then
        # Create virtual interfaces and hook in_veth into out_veth
        # and vice versa.
        ip link add name $in_veth type veth peer name $out_veth

        # Allow frames to be larger than default.
        # This allows testing of jumbo frames with bmv2.
        # https://github.com/p4lang/behavioral-model/blob/master/tools/veth_setup.sh
        ip link set $in_veth mtu 9500
        ip link set $out_veth mtu 9500

        # Linux kernel automatically sends IPv6 headers if IPv6 is enabled.
        # This will make our P4 programs complicated or malfunction,
        # since they mostly use IPv4 headers.
        # Disable IPv6 to avoid this.
        sysctl net.ipv6.conf.${in_veth}.disable_ipv6=1
        sysctl net.ipv6.conf.${out_veth}.disable_ipv6=1

        # Start the virtual interfaces.
        ip link set dev $in_veth up
        ip link set dev $out_veth up
    fi
done
