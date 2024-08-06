#!/bin/bash

EXP_TIME="12h"

# Perf comparison: cumulative FS operations and unique abstract states overtime
# 1. Ext4, 2. XFS, 3. BtrFS, 4. Ext4 vs. XFS, 5. Ext4 vs. XFS vs. BtrFS 

CURRENT_DIR=$(pwd)

FS_TYPES=("Ext4" "XFS" "BtrFS" "Ext4-XFS" "Ext4-XFS-BtrFS")
METIS_AGRS=("ext4:2048" "xfs:16384" "btrfs:16384" "ext4:2048:xfs:16384" "ext4:2048:xfs:16384:btrfs:16384")

# Get the length of the FS_TYPES
NUMFS=${#FS_TYPES[@]}

for i in "${!FS_TYPES[@]}"; do
    FSNAME = ${FS_TYPES[$i]}
    echo "Processing file system(s) with Metis at index $i: $FSNAME"
    # Step 1: Run the Metis with SPIN for a predefined time
    cd ../fs-state/mcfs_scripts
    ./multi_fs.sh ${METIS_AGRS[$i]} $EXP_TIME

    # Step 2: Collect the performance results
    cd ..
    mkdir -p tos-expt-metis-perf-time-chart-$FSNAME-${EXP_TIME}-logs
    mv *.log *.csv *.gz *.txt *.img script* swarm_done_s* tos-expt-metis-perf-time-chart-$FSNAME-${EXP_TIME}-logs
done

echo "All completed: $NUMFS"
