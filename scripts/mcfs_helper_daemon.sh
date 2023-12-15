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

echoerr() { echo "$@" 1>&2; }

# Array of free directory (free partition)
FREE_PARTS=("/disk2" "/disk3")

# Current path
CURR_PATH="$PWD"

# Time to add in the directory
EXP_TIME=$(date +%Y%m%d-%H%M%S)

# Reserved space in KiB for each partition
# Current 5GB
RSVD_SPC_KB=$((5 * 1024 * 1024))

# Set sleep interval 30 minutes
INTVL_MINS=30
SLEEP_INTVL=$(($INTVL_MINS * 60))

# File to save dmesg error info
DMESG_ERR_LOG="$CURR_PATH/dmesg-error-$d.log"

# A while loop
while true; do
    PART_TO_USE=""
    # Get current available disk using a loop
    for PART_NAME in "${FREE_PARTS[@]}"
    do
        AVAIL_SPC_KB=$(df -P $PART_NAME | tail -1 | awk '{print $4}')
        if [ "$AVAIL_SPC_KB" -gt "$RSVD_SPC_KB" ]; then
            PART_TO_USE=$PART_NAME
            break
        fi
    done
    # Check if PART_TO_USE is empty -- no available partition to use
    if [ -z "$PART_TO_USE" ]
    then
        echoerr "NO PARTITION AND DIR HAVE ENOUGH SPACE NOW!"
        break
    fi
    # Populate the dir to move into
    SAVED_DIR="$PART_TO_USE/MCFS-Logs-Backup-$EXP_TIME"
    # Move all log.gz to back-up dir if they exist
    if compgen -G "${CURR_PATH}/*.log.gz" > /dev/null; then
        mv "${CURR_PATH}/*.log.gz" $SAVED_DIR
    fi
    # TODO: found old pan logs and move them
    # Check dmesg to get any error message
    journalctl -p 3 -kexS -${INTVL_MINS}min >> $DMESG_ERR_LOG

    sleep $SLEEP_INTVL
done

