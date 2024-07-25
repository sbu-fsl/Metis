#!/bin/bash


# Initialize an empty array for job files
job_files=()

# Populate the array with job files that match the pattern
for file in `hostname`-swarm-job.yaml; do
    # Check if the file matches the pattern and exists
    if [[ -f "$file" ]]; then
        job_files+=("$file")
    fi
done

# Check if any job files were found
if [ ${#job_files[@]} -eq 0 ]; then
    echo "No job files found."
    exit 0
fi


# Iterate over job files and apply each one
for file in "${job_files[@]}"; do
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

