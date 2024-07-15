#!/bin/bash

# Define the base names for your scripts
scripts=("script0" "script1" "script2" "script3" "script4" "script5")

# GitHub Container Registry URL
registry_url="ghcr.io/divyaankt"

# Loop over each script and build and push the Docker images
for script in "${scripts[@]}"; do
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

