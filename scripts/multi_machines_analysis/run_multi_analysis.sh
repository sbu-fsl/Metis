#!/bin/bash

set -e  # Exit on error

MASTER="yifeilatest3"
CLIENTS=("yifeilatest4" "yifeilatest5")

CLIENT_DIR="/mcfs-swarm"
EACH_VT_CNT=6
CLIENT_SWARM_DIR="/mcfs-swarm/nfs4mc/scripts/multi_machines_analysis"

# Part 1: For each machine, go to logs directory, and decompress output-pan*.log.gz

# Function to decompress .gz files on a given node
decompress_on_node() {
    local node=$1
    ssh "$node" "find ${CLIENT_DIR} -name 'output-pan*.log.gz' -exec gunzip -k {} \;"
}

## For master machine, decompress at local fs-state directory
cd ../../fs-state 
gzip -d output-pan*.log.gz &

## For client machines, decompress at remote mcfs-swarm directory
for CLIENT in "${CLIENTS[@]}"; do
    decompress_on_node $CLIENT &
done

# Wait for all background decompression jobs to finish
wait

echo "All decompression jobs finished."

# Part 2: Extract abstract states from raw output log files

## Master machine
cd /mcfs-swarm/nfs4mc/scripts/multi_machines_analysis
python3 multi_extract_absfs.py $EACH_VT_CNT ../../fs-state/output-pan\*.log &

## Client machines
## For client machines, extract abstract states from logs remotely
for CLIENT in "${CLIENTS[@]}"; do
    ssh $CLIENT "cd $CLIENT_SWARM_DIR && python3 multi_extract_absfs.py $EACH_VT_CNT ../../fs-state/output-pan\*.log" &
done

# Wait for all background absfs extraction jobs to finish
wait
