#!/bin/bash

# Array of deployment files
deployment_files=("script0-deployment.yaml" "script1-deployment.yaml" "script2-deployment.yaml" "script3-deployment.yaml" "script4-deployment.yaml" "script5-deployment.yaml")

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

