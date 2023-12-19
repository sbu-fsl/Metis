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

# Run this script in fs-state folder (i.e., ../scripts/run_various_VTs.sh)

HOUR_LIMIT=4
VT_NUMS=(2 4 6 8 10 12 14 16)

declare -A HOST_DISK_MAP
HOST_DISK_MAP+=( ["sgdp03"]="/ssd" ["sgdp04"]="/disk3" ["sgdp06"]="/ssd" )

HOST_NAME=$(hostname)
AVAIL_PART=${HOST_DISK_MAP[${HOST_NAME}]}

EXP_TIME=$(date +%Y%m%d-%H%M%S)

SWARM_CONF="swarm.lib"

make clean
./stop.sh > /dev/null 2>&1
rmmod brd
./loadmods.sh

for VT_NUM in ${VT_NUMS[@]}; do
    echo "Currently processing VT number: ${VT_NUM}..."
    LOGS_DIR="$AVAIL_PART/$HOST_NAME-$VT_NUM-saved-$EXP_TIME"
    # Create save logs directory
    mkdir -p $LOGS_DIR
    # Stop and clean any running MCFS resources
    # Make the current machine clean state
    ./stop.sh > /dev/null 2>&1
    rm -r /mnt/test-* > /dev/null 2>&1
    make clean
    sed -i "16 s/^k\t1\t[0-9]\+.*/k\t1\t${VT_NUM}/" ${SWARM_CONF}
    sed -i "20 s/^cpus\t[0-9]\+.*/cpus\t${VT_NUM}/" ${SWARM_CONF}
    timeout ${HOUR_LIMIT}h ./setup_swarm.sh -f ext4:256:ext2:256 -n $VT_NUM
    mv script* *.log *.log.gz *.txt *.csv $LOGS_DIR
done
