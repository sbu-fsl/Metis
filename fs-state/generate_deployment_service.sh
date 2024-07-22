#!/bin/bash

# Initialize an empty array to store script names
scripts=()

# Loop over each file matching Dockerfile_script*
for dockerfile in Dockerfile_script*; do
    # Extract the script number from the Dockerfile name
    script_number=$(echo "$dockerfile" | grep -o '[0-9]\+')

    # Add the script to the array if the number was found
    if [ -n "$script_number" ]; then
        scripts+=("script${script_number}")
    fi
done

# Function to generate the deployment YAML
generate_deployment_yaml() {
    local script=$1

    cat <<EOL > ${script}-deployment.yaml
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
        securityContext:
          privileged: true
      initContainers:
      - name: install-packages
        image: ubuntu:latest
        command: ["sh", "-c", "apt-get update && apt-get install -y bash gcc g++ make libssl-dev libstdc++6 libstdc++-9-dev zlib1g-dev libxxhash-dev libboost-filesystem-dev libboost-system-dev libgoogle-perftools4 && rm -rf /var/lib/apt/lists/* && mknod /dev/ram0 b 1 0"]
        volumeMounts:
        - name: include-volume
          mountPath: /scripts/include
        - name: logs-volume
          mountPath: /scripts/logs
      volumes:
      - name: include-volume
        hostPath:
          path: /mnt/mcfs/nfs4mc/include
      - name: logs-volume
        hostPath:
          path: /mnt/mcfs/swarm_logs
      imagePullSecrets:
      - name: regcred
EOL
}

# Function to generate the service YAML
generate_service_yaml() {
    local script=$1

    cat <<EOL > ${script}-service.yaml
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
EOL
}

# Loop over each script and generate the respective YAML files
for script in "${scripts[@]}"; do
    generate_deployment_yaml ${script}
    generate_service_yaml ${script}
done

echo "Deployment and Service YAML files generated for scripts: ${scripts[@]}"

