#!/bin/bash

# Initialize an empty array to store script names
scripts=()
mapping_file="hostname_script_mapping.txt"

# Loop over each file matching Dockerfile_script*
for dockerfile in Dockerfile_script*; do
    # Extract the script number from the Dockerfile name
    script_number=$(echo "$dockerfile" | grep -o '[0-9]\+')

    # Add the script to the array if the number was found
    if [ -n "$script_number" ]; then
        scripts+=("script${script_number}")
    fi
done

current_host=$(hostname)

# File to store all combined deployment configurations
swarm_deployment_file="$current_host-swarm-deployment.yaml"
swarm_service_file="$current_host-swarm-service.yaml"
swarm_job_file="$current_host-swarm-job.yaml"

# Clear the contents of the combined files if they exist
> $swarm_deployment_file
> $swarm_service_file
> $swarm_job_file

# Read the hostname_script_mapping.txt file and store the mappings in an associative array
declare -A script_to_hostname_map

while IFS=' : ' read -r hostname script; do
    # Trim whitespace
    hostname=$(echo $hostname | xargs)
    script=$(echo $script | xargs)
    script_to_hostname_map["$script"]="$hostname"
done < $mapping_file

generate_job_yaml() {
    local script=$1
    local dev_number=$(echo "$script" | grep -o '[0-9]*')
	
    # Fetch the hostname for the given script from the associative array
    local hostname="${script_to_hostname_map[$script]}"

    # Check if the hostname was found for the script
    if [ -z "$hostname" ]; then
        echo "Error: No hostname found for script $script"
        return 1
    fi

    cat <<EOL >> $swarm_job_file
apiVersion: batch/v1
kind: Job
metadata:
  name: ${script}-job
spec:
  completions: 1
  parallelism: 1
  backoffLimit: 10
  template:
    metadata:
      labels:
        app: ${script}
    spec:
      restartPolicy: OnFailure
      containers:
      - name: ${script}
        image: ghcr.io/divyaankt/${script}:latest
        command: ["sh", "-c", "./${script} > /scripts/logs/${script}.out 2> /scripts/logs/${script}.err"]
        resources:
          requests:
            memory: "500Mi"
            cpu: "1"
            ephemeral-storage: "500Mi"
          limits:
            memory: "1Gi"
            cpu: "1"
	    ephemeral-storage: "1Gi"
        volumeMounts:
        - name: include-volume
          mountPath: /scripts/include
        - name: logs-volume
          mountPath: /scripts/logs
        - name: ramdisk-volume
          mountPath: /dev/ram0
        securityContext:
          privileged: true
#      affinity:
#        nodeAffinity:
#          requiredDuringSchedulingIgnoredDuringExecution:
#            nodeSelectorTerms:
#            - matchExpressions:
#              - key: kubernetes.io/hostname
#                operator: In
#                values:
#                - ${hostname}
      volumes:
      - name: include-volume
        hostPath:
          path: /mnt/mcfs/nfs4mc/include
      - name: logs-volume
        hostPath:
          path: /mnt/mcfs/swarm_logs
      - name: ramdisk-volume
        hostPath:
          path: /dev/ram$dev_number
      imagePullSecrets:
      - name: regcred
---
EOL
}

generate_deployment_yaml() {
    local script=$1
    local dev_number=$(echo "$script" | grep -o '[0-9]*')

    cat <<EOL >> $swarm_deployment_file
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ${script}-deployment
spec:
  replicas: 1
  selector:
    matchLabels:
      app: ${script}
  template:
    metadata:
      labels:
        app: ${script}
    spec:
      containers:
      - name: ${script}
        image: ghcr.io/divyaankt/${script}:latest
        command: ["sh", "-c", "./${script} > /scripts/logs/${script}.out 2> /scripts/logs/${script}.err"]
        volumeMounts:
        - name: include-volume
          mountPath: /scripts/include
        - name: logs-volume
          mountPath: /scripts/logs
        - name: ramdisk-volume
          mountPath: /dev/ram0
        securityContext:
          privileged: true
      volumes:
      - name: include-volume
        hostPath:
          path: /mnt/mcfs/nfs4mc/include
      - name: logs-volume
        hostPath:
          path: /mnt/mcfs/swarm_logs
      - name: ramdisk-volume
        hostPath:
          path: /dev/ram$dev_number
      imagePullSecrets:
      - name: regcred
---
EOL
}


# Function to generate the service YAML
generate_service_yaml() {
    local script=$1
	
    cat <<EOL >> $swarm_service_file
apiVersion: v1
kind: Service
metadata:
  name: ${script}
spec:
  selector:
    app: ${script}
  ports:
    - protocol: TCP
      port: 80
      targetPort: 8080
---
EOL
}

# Loop over each script and generate the respective YAML files
for script in "${scripts[@]}"; do
    # generate_deployment_yaml ${script}
    # generate_service_yaml ${script}
    generate_job_yaml ${script}
done

echo "Swarm job YAML files generated for scripts: ${scripts[@]}"

