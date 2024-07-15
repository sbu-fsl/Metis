#!/bin/bash

# Ensure environment variables are set
if [[ -z "$DOCKER_SERVER" || -z "$DOCKER_USERNAME" || -z "$DOCKER_PASSWORD" || -z "$DOCKER_EMAIL" ]]; then
  echo "One or more required environment variables are missing."
  exit 1
fi

# Create Docker config JSON
DOCKER_CONFIG_JSON=$(jq -n \
  --arg server "$DOCKER_SERVER" \
  --arg username "$DOCKER_USERNAME" \
  --arg password "$DOCKER_PASSWORD" \
  --arg email "$DOCKER_EMAIL" \
  '{
    "auths": {
      ($server): {
        "username": $username,
        "password": $password,
        "email": $email,
        "auth": ($username + ":" + $password | @base64)
      }
    }
  }')

# Encode Docker config JSON in base64
DOCKER_CONFIG_JSON_BASE64=$(echo "$DOCKER_CONFIG_JSON" | base64 -w 0)

# Substitute the base64 encoded Docker config JSON into the YAML template
cat <<EOF > reg-secret.yaml
apiVersion: v1
kind: Secret
metadata:
  name: regcred
data:
  .dockerconfigjson: $DOCKER_CONFIG_JSON_BASE64
type: kubernetes.io/dockerconfigjson
EOF

# Apply the secret to Kubernetes
kubectl apply -f reg-secret.yaml

# Clean up
rm reg-secret.yaml

