#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

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

################ Part 3: Copy extracted abstract states from client machines to master machine

## Copy time-absfs-{hostname}-VT{allVT}-pan(VTnum).csv from clients to the master
for CLIENT in "${CLIENTS[@]}"; do
    scp $CLIENT:"$SWARM_SCRIPT_DIR"/time-absfs-$CLIENT-*-pan*.csv . &
done

wait

echo "All abstract states csv copying jobs finished."

################ Part 4: Rename abstract states csv files for analysis 

## Correct total VT count (e.g., 18 which is 3 machines * 6 VTs per machine)
TOTVM=$(((${#CLIENTS[@]} + 1) * EACH_VT_CNT))

rename "s/VT$EACH_VT_CNT/VT$TOTVM/" time-absfs-*-VT$EACH_VT_CNT-pan*.csv

for index in "${!CLIENTS[@]}"; do
    CLIENT="${CLIENTS[$index]}"
    for file in time-absfs-$CLIENT-VT*-pan*.csv; do
        # Extract the pan number before .csv using awk (e.g., time-absfs-yifeilatest4-VT6-pan3.csv, num=3)
        num=$(echo "$file" | awk -F'pan' '{print $2}' | cut -d '.' -f1)
        # Increment the number by 6 every time
        new_num=$((num + 6 * (index + 1)))
        # Construct the new filename using bash's string replacement
        new_file="${file/pan$num.csv/pan$new_num.csv}"
        # Rename the file
        mv "$file" "$new_file"    
    done 
done

## Rename to master hostname
for CLIENT in "${CLIENTS[@]}"; do
    rename "s/$CLIENT/$MASTER/" time-absfs-$CLIENT-VT*-pan*.csv
done 

################ Part 5: Perform analysis 

./multi_analyze_all.py -m 147 -n 18 > results-yifeilatest345-Overall-VT18-each6-147hours-2023-1012.csv
