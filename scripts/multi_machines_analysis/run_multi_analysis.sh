#!/bin/bash

VT_NUMS=(2 4 6 8 10 12 14 16)

declare -A HOST_DISK_MAP
HOST_DISK_MAP+=( ["sgdp03"]="/ssd" ["sgdp04"]="/disk3" ["sgdp06"]="/ssd" )

HOST_NAME=$(hostname)
AVAIL_PART=${HOST_DISK_MAP[${HOST_NAME}]}
MAX_HOURS=4

for VT_NUM in ${VT_NUMS[@]}; do
    echo "Processing $VT_NUM..."
    # Extract absfs csv files
    # First arg: number of VTs, Second arg: 
    ./multi_extract_absfs.py $VT_NUM $AVAIL_PART/$HOST_NAME-$VT_NUM-saved-202204*/output-pan\*.log
    # Produce results csv
    multi_analyze_all.py -m $MAX_HOURS -n $VT_NUM > results-$HOST_NAME-VT${VT_NUM}.csv
done
