#!/bin/bash

# Initialize an empty array for deployment files
deployment_names=()

# Populate the array with deployment files that match the pattern
for file in `hostname`-swarm-deployment.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        # Remove the .yaml extension from the filename
        #base_name="${file%.yaml}"
	deployment_names+=("$file")
    fi
done

# Check if any deployment files were found
if [ ${#deployment_names[@]} -eq 0 ]; then
    echo "No deployment files found."
    exit 0
fi


# Iterate over deployment names and delete each deployment
for name in "${deployment_names[@]}"; do
    echo "Deleting deployment $name..."
    kubectl delete -f "$name"

    if [ $? -ne 0 ]; then
        echo "Failed to delete deployment $name"
        exit 1
    fi

    echo "Service $name successfully deleted"
done

