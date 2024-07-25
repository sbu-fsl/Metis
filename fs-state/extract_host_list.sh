#!/bin/bash

input_file="swarm.lib"

# Read the cpus line
cpus_line=$(grep "^cpus" $input_file)

# Extract the hostnames
hosts=$(echo $cpus_line | grep -oE '[^[:space:]]+:[0-9]+' | sed 's/:[0-9]*//g')

grep "^cpus" $input_file# Include the current host
current_host=$(hostname)
hosts=$(echo -e "$hosts\n$current_host" | sort -u)

# Print the list of hosts
echo "List of hosts:"
echo "$hosts"

