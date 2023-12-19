#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

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
    ./multi_analyze_all.py -m $MAX_HOURS -n $VT_NUM > results-$HOST_NAME-VT${VT_NUM}.csv
done
