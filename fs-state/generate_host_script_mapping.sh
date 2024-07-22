#!/bin/bash

swarm_config_file="swarm.lib"
swarm_script_file="mcfs-main.pml.swarm"
mapping_file="hostname_script_mapping.txt"
temp_file="temp_lines.txt"

# Initialize an empty output file
echo -n > $mapping_file

# Extract the value of S from the mcfs-main.pml.swarm file
script_name=$(grep '^S=' $swarm_script_file | sed 's/^S=//')

# Debug: Print the value of S to verify
# echo "Extracted S value: $script_name"

# Extract the case block after the comment '# end of preparation'
sed -n '/# end of preparation/,/esac/p' $swarm_script_file > $temp_file

# Debug: Print extracted lines to verify
# echo "Extracted lines:"
# cat $temp_file
# echo

# Read the cpus line from swarm.lib
cpus_line=$(grep "^cpus" $swarm_config_file)

# Extract the hostnames followed by a colon and a number
hosts=$(echo $cpus_line | grep -oE '[^[:space:]]+:[0-9]+' | sed 's/:[0-9]*//g')

# Include the current host
current_host=$(hostname)
hosts=$(echo -e "$hosts\n$current_host" | sort -u)

# Print the list of hosts for debugging
# echo "List of hosts:"
# echo "$hosts"
# echo

# Read the extracted lines and create the mapping
hostname=""
while IFS= read -r line; do
    # Debug: Print each line being processed
    # echo "Processing line: $line"

    # Remove leading and trailing whitespace for accurate processing
    line=$(echo "$line" | sed 's/^[ \t]*//;s/[ \t]*$//')

    # Check for hostname lines using the list of hosts
    if echo "$hosts" | grep -qw "$(echo $line | sed 's/).*//')"; then
        hostname=$(echo $line | sed -e 's/).*//')
		# echo "Detected hostname: $hostname"
    elif [[ $line == *"*)" ]]; then
        hostname=$(hostname)
        # echo "Default case detected. Using hostname: $hostname"
    elif [[ $line == sh* ]]; then
        # Extract the script name with the placeholder ${S}
        script=$(echo $line | sed -e 's/^.*sh[[:space:]]*\.\///' -e 's/[[:space:]]*>.*$//')
        # Replace ${S} with the actual value of S and remove double quotes
        script=$(echo $script | sed "s/\${S}/$script_name/g" | tr -d '"')
        # echo "Detected script: $script"
        echo "$hostname : $script" >> $mapping_file
    fi
done < $temp_file

# Clean up
rm -f $temp_file

echo "Mapping written to $mapping_file"
