#!/bin/bash

# Loop over each script matching the pattern script[0-9].sh
for script in script[0-9]; do
  # Extract the script number (e.g., script0.sh -> 0)
  script_number=$(echo $script | grep -o '[0-9]')

  # Create a Dockerfile for each script
  cat <<EOL > Dockerfile_script${script_number}
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

done

echo "Dockerfiles created for each script."
