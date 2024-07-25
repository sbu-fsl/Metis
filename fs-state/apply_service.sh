#!/bin/bash


# Initialize an empty array for deployment files
service_files=()

# Populate the array with service files that match the pattern
for file in `hostname`-swarm-service.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        service_files+=("$file")
    fi
done

# Check if any service files were found
if [ ${#service_files[@]} -eq 0 ]; then
    echo "No service files found."
    exit 0
fi


# Iterate over service files and apply each one
for file in "${service_files[@]}"; do
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

