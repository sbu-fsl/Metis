#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Pei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# kill processes that might reserve some resource
pkill -9 -f "./mcfs-main.pml"
pkill -9 -f "./mcfs-main.pml.swarm"
pkill -9 -f "sh ./script"
# Need to kill both "pan" and "pan[0-9+]" processes
pkill -9 -f "./pan"

# Function to unmount a device with retries
unmount_with_retry() {
    local target=$1
    local max_retries=5
    local retry_delay=2 # seconds
    local attempt=1

    while [ $attempt -le $max_retries ]; do
        if mountpoint -q "$target"; then
            echo "Attempting to unmount $target (Attempt $attempt/$max_retries)..."
            if umount -l "$target"; then
                echo "$target unmounted successfully."
                break
            else
                echo "Failed to unmount $target. Retrying after $retry_delay seconds..."
                sleep $retry_delay
            fi
        else
            echo "$target is not mounted or does not exist."
            break
        fi
        ((attempt++))
    done

    if [ $attempt -gt $max_retries ]; then
        echo "Failed to unmount $target after $max_retries attempts."
    fi
}

# Unmount all the devices and mount points

# Array of devices and mount points to unmount
devices_and_mounts=(/dev/ram* /dev/mtdblock* /mnt/test-*)

# Loop through each device/mount point and attempt to unmount
for item in "${devices_and_mounts[@]}"; do
    # Glob expansion and iteration over each path
    for path in $item; do
        # Existence check before attempting unmount
        if [ -e "$path" ] || [[ "$path" =~ /dev/ram ]] || [[ "$path" =~ /dev/mtdblock ]]; then
            unmount_with_retry "$path"
        else
            echo "Skipping non-existent path: $path"
        fi
    done
done
