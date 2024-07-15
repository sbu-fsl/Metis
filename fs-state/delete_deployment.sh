#!/bin/bash

# Array of deployment names (without the .yaml extension)
deployment_names=("script0-deployment" "script1-deployment" "script2-deployment" "script3-deployment" "script4-deployment" "script5-deployment")

# Iterate over deployment names and delete each deployment
for name in "${deployment_names[@]}"; do
    echo "Deleting deployment $name..."
    kubectl delete deployment "$name"

    if [ $? -ne 0 ]; then
        echo "Failed to delete deployment $name"
        exit 1
    fi

    echo "Deployment $name successfully deleted"
done

