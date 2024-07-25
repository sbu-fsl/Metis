#!/bin/bash

# Initialize an empty array for service files
service_names=()

# Populate the array with service files that match the pattern
for file in `hostname`-swarm-service.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        # Remove the .yaml extension from the filename
        #base_name="${file%.yaml}"
	service_names+=("$file")
    fi
done

# Check if any service files were found
if [ ${#service_names[@]} -eq 0 ]; then
    echo "No service files found."
    exit 0
fi


# Iterate over deployment names and delete each deployment
for name in "${service_names[@]}"; do
    echo "Deleting service $name..."
    kubectl delete -f "$name"

    if [ $? -ne 0 ]; then
        echo "Failed to delete service $name"
        exit 1
    fi

    echo "Service $name successfully deleted"
done

