#!/bin/bash

set -e  # Exit on error

MASTER="yifeilatest3"
CLIENTS=("yifeilatest4" "yifeilatest5")

CLIENT_DIR="/mcfs-swarm"
EACH_VT_CNT=6
MASTER_DIR="/mcfs-swarm/nfs4mc/fs-state"
SWARM_SCRIPT_DIR="/mcfs-swarm/nfs4mc/scripts/multi_machines_analysis"


################ Part 1: For each machine, go to logs directory, and decompress output-pan*.log.gz

# Function to decompress .gz files that are not yet decompressed on a given node
decompress_on_node() {
    local node=$1
    ssh $node "
        for gzfile in \$(find $CLIENT_DIR -name 'output-pan*.log.gz'); do
            file_without_gz=\${gzfile%.gz}
            if [ ! -f \$file_without_gz ]; then
                gunzip -k \$gzfile
            else
                echo \"\$gzfile is already decompressed\"
            fi
        done
    "
}

## For master machine, decompress at local fs-state directory (MASTER_DIR)

# For each .gz file in the directory
for gzfile in "$MASTER_DIR"/output-pan*.log.gz; do
    # Extract the filename without the .gz extension
    file_without_gz="${gzfile%.gz}"
    # Check if the decompressed file exists
    if [[ ! -f "$file_without_gz" ]]; then
        # Decompress the file without deleting the original .gz file in background
        gunzip -k "$gzfile" &
    else
        echo "$gzfile is already decompressed"
    fi
done

## For client machines, decompress at remote mcfs-swarm directory
for CLIENT in "${CLIENTS[@]}"; do
    decompress_on_node $CLIENT &
done

# Wait for all background decompression jobs to finish
wait

echo "All decompression jobs finished."

################ Part 2: Extract abstract states from raw output log files

## Master machine (local)
cd $SWARM_SCRIPT_DIR

python3 multi_extract_absfs.py $EACH_VT_CNT ../../fs-state/output-pan\*.log &

## Client machines (remote via ssh)
## For client machines, extract abstract states from logs remotely
for CLIENT in "${CLIENTS[@]}"; do
    ssh $CLIENT "cd $SWARM_SCRIPT_DIR && python3 multi_extract_absfs.py $EACH_VT_CNT ../../../output-pan\*.log" &
done

# Wait for all background absfs extraction jobs to finish
wait

echo "All abstract states extraction jobs finished."

# ################ Part 3: Copy extracted abstract states from client machines to master machine

## Copy time-absfs-{hostname}-VT{allVT}-pan(VTnum).csv from clients to the master
for CLIENT in "${CLIENTS[@]}"; do
    scp $CLIENT:"$SWARM_SCRIPT_DIR"/time-absfs-$CLIENT-*-pan*.csv . &
done

wait

echo "All abstract states csv copying jobs finished."
