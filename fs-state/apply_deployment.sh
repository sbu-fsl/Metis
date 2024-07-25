#!/bin/bash


# Initialize an empty array for deployment files
deployment_files=()

# Populate the array with deployment files that match the pattern
for file in `hostname`-swarm-deployment.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        deployment_files+=("$file")
    fi
done

# Check if any deployment files were found
if [ ${#deployment_files[@]} -eq 0 ]; then
    echo "No deployment files found."
    exit 0
fi


# Iterate over deployment files and apply each one
for file in "${deployment_files[@]}"; do
    # Check if file exists
    if [ ! -f "$file" ]; then
        echo "Error: File $file does not exist"
        continue
    fi

    echo "Applying $file..."
    kubectl apply -f "$file"

    if [ $? -ne 0 ]; then
        echo "Failed to apply $file"
        exit 1
    fi

    echo "$file successfully applied"
done

