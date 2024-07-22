#!/bin/bash

# Define the GitHub Container Registry URL
registry_url="ghcr.io/divyaankt"

# Populate the scripts array based on the presence of Dockerfile_scriptX files
scripts=()
for file in Dockerfile_script[0-9]*; do
    if [[ -f $file ]]; then
        # Extract the script number from the filename
        script_number=$(echo $file | grep -o '[0-9]\+')

	# Add the script to the array if the number was found
        if [ -n "$script_number" ]; then
          scripts+=("script${script_number}")
	fi
    fi
done

# Check if there are no scripts to process
if [ ${#scripts[@]} -eq 0 ]; then
    echo "No Dockerfile_script* files found in the current directory."
    exit 1
fi

# Loop over each script and build and push the Docker images
for script in "${scripts[@]}"; do

    # Check if Dockerfile exists
    dockerfile="Dockerfile_script${script#script}"
    if [[ ! -f $dockerfile ]]; then
        echo "Dockerfile ${dockerfile} does not exist. Skipping ${script}."
        continue
    fi

    # Build the Docker image
    docker build -t ${registry_url}/${script}:latest -f Dockerfile_${script} .

    # Check if the build was successful
    if [ $? -eq 0 ]; then
        echo "Successfully built ${script}"
    else
        echo "Failed to build ${script}"
        exit 1
    fi

    # Push the Docker image to GitHub Container Registry
    docker push ${registry_url}/${script}:latest

    # Check if the push was successful
    if [ $? -eq 0 ]; then
        echo "Successfully pushed ${script}"
    else
        echo "Failed to push ${script}"
        exit 1
    fi
done

echo "Docker images for scripts: ${scripts[@]} have been built and pushed to ${registry_url}"

