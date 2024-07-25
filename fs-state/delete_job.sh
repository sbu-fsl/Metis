#!/bin/bash

# Initialize an empty array for job files
job_names=()

# Populate the array with job files that match the pattern
for file in `hostname`-swarm-job.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        # Remove the .yaml extension from the filename
        #base_name="${file%.yaml}"
	job_names+=("$file")
    fi
done

# Check if any job files were found
if [ ${#job_names[@]} -eq 0 ]; then
    echo "No job files found."
    exit 0
fi


# Iterate over job names and delete each job
for name in "${job_names[@]}"; do
    echo "Deleting job $name..."
    kubectl delete -f "$name"

    if [ $? -ne 0 ]; then
        echo "Failed to delete job $name"
        exit 1
    fi

    echo "Service $name successfully deleted"
done

