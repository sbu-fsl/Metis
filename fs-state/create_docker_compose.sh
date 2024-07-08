#!/bin/bash

# Check and create the logs directory if it doesn't exist
if [ ! -d /mnt/mcfs/swarm_logs ]; then
  mkdir -p /mnt/mcfs/swarm_logs
  echo "Directory /mnt/mcfs/swarm_logs created."
else
  echo "Directory /mnt/mcfs/swarm_logs already exists."
fi

# Start the docker-compose.yml file
cat <<EOL > docker-compose.yml
version: '3.8'

services:
EOL

# Loop over each script matching the pattern script[0-9].sh
for script in script[0-9]*; do
  # Extract the script number (e.g., script17 -> 17)
  script_number=$(echo $script | grep -o '[0-9]\+')

  # Append to the docker-compose.yml file
  cat <<EOL >> docker-compose.yml
  script${script_number}:
    build:
      context: .
      dockerfile: Dockerfile_script${script_number}
    user: root
    container_name: Swarm${script_number}_container
    volumes:
      - /mnt/mcfs/nfs4mc/include:/scripts/include
      - /mnt/mcfs/swarm_logs:/scripts/logs
    privileged: true
EOL

done

echo "docker-compose.yml file created."
