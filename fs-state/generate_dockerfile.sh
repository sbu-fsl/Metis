#!/bin/bash

# File containing hostname:scriptname mapping
mapping_file="hostname_script_mapping.txt"

# Get the current hostname
current_hostname=$(hostname)

# Extract the list of scripts mapped to the current hostname
scripts_to_build=$(grep "${current_hostname} :" $mapping_file | awk -F ' : ' '{print $2}')

# Check if there are any scripts to build
if [ -z "$scripts_to_build" ]; then
    echo "No scripts mapped to the current hostname (${current_hostname}). Exiting."
    exit 1
fi


# Loop over each script matching the pattern script[0-9].sh
for script in $scripts_to_build; do
   
  # Check if the script file exists
  if [ -f "${script}" ]; then
    # Extract the script number (e.g., script0 -> 0)
    script_number=$(echo $script | grep -o '[0-9]*')

  # Create a Dockerfile for each script
  cat <<EOL > "Dockerfile_script${script_number}"
# Dockerfile for ${script}
FROM ubuntu:latest

# Explicitly set the user to root
USER root

# Install necessary packages
RUN apt-get update && apt-get install -y \
    bash \
    gcc \
    g++ \
    make \
    libssl-dev \
    libstdc++6 \
    libstdc++-9-dev \
    zlib1g-dev \
    libxxhash-dev \
    libboost-filesystem-dev \
    libboost-system-dev \
    libgoogle-perftools4 \
    && rm -rf /var/lib/apt/lists/*

# Create the logs directory
RUN mkdir -p /scripts/logs /scripts/include /scripts/fs-state

# Copy Metis/fs-state folder
COPY . /scripts/fs-state

# Set the working directory
WORKDIR /scripts/fs-state

# Create /dev/ram0
RUN mknod /dev/ram0 b 1 0

# Make the script and the pan executable executable
RUN chmod +x ${script} pan*

# Command to run the script and redirect output
CMD ["sh", "-c", "./${script} > /scripts/logs/${script}.out 2> /scripts/logs/${script}.err"]
EOL

    echo "Dockerfile created for ${script}."
  else
    echo "Script ${script} not found. Skipping."
  fi
done

echo "Dockerfiles creation process completed."
