#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Divyaank Tiwari
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

MOUNTPOINT="/mnt/test-jfs-i1-s0"
devname="/dev/ram1"
size_kb=$((16 * 1024))

loadmods() {

    # Unload brd ramdisk kernel module
    if lsmod | grep -q "^brd"; then
        echo "brd module is loaded. Unloading it now."
        if rmmod brd; then
            echo "Successfully removed brd module."
        else
            echo "Failed to remove brd module."
            exit 1
        fi
    fi

    # Load the brd module with the specified RAM disk size
    modprobe brd rd_nr=2 rd_size=$size_kb

    # Verify if the module is loaded
    if lsmod | grep -q brd; then
        echo "brd module loaded successfully."
    else
        echo "Failed to load brd module."
        exit 1
    fi

    # Check for the creation of RAM disk devices
    if ls /dev/ram* 1> /dev/null 2>&1; then
        echo "RAM disk devices created:"
        ls -l /dev/ram*
    else
        echo "No RAM disk devices found."
        exit 1
    fi

    # Verify the size of the RAM disk
    RAM0_SIZE=$(sudo blockdev --getsize64 /dev/ram0)
    EXPECTED_SIZE=$((size_kb * 1024))

    if [ "$RAM0_SIZE" -eq "$EXPECTED_SIZE" ]; then
        echo "RAM disk size is correct: ${RAM0_SIZE} bytes."
    else
        echo "RAM disk size is incorrect: ${RAM0_SIZE} bytes (expected ${EXPECTED_SIZE} bytes)."
        exit 1
    fi

    echo "RAM disk setup completed successfully."

}

populate_mountpoint() {
    
    # Check if any file-system has been mounted on the folder
    if mount | grep -q "$MOUNTPOINT"; then
        echo "A filesystem is mounted on $MOUNTPOINT. Unmounting..."
        # Unmount the filesystem
        umount -f "$MOUNTPOINT"
        if [ $? -eq 0 ]; then
            echo "Successfully unmounted $MOUNTPOINT."
        else
            echo "Failed to unmount $MOUNTPOINT. Please check for issues."
            return 1
        fi
    else
        echo "No filesystem is mounted on $MOUNTPOINT."
    fi

    # Create the required directory
    mkdir -p "$MOUNTPOINT"
    if [ $? -eq 0 ]; then
        echo "Successfully created directory $MOUNTPOINT."
    else
        echo "Failed to create directory $MOUNTPOINT. Please check for issues."
        return 1
    fi
}

check_device() {
    local devname="$1"
    local size_kb="$2"
    local exp_size_bytes=$((size_kb * 1024))

    # Open the device (check if the file exists and is readable)
    if [ ! -r "$devname" ]; then
        echo "Cannot open $devname (err=$(strerror $?))"
        return 1
    fi

    # Get device info
    if ! stat --printf='' "$devname" 2>/dev/null; then
        echo "Cannot stat $devname (err=$(strerror $?))"
        return 1
    fi

    # Check if it's a block device
    if [ ! -b "$devname" ]; then
        echo "$devname is not a block device."
        return 1
    fi

    # Get the size of the device in bytes
    devsize=$(blockdev --getsize64 "$devname" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "Cannot get size of $devname (err=$(strerror $?))"
        return 1
    fi

    # Check if the device size is smaller than expected
    if [ "$devsize" -lt "$exp_size_bytes" ]; then
        echo "$devname is smaller than expected (expected ${size_kb} KB, got $((devsize / 1024)) KB)."
        return 1
    fi

    return 0
}

setup_jfs() {
    # Zero out the device
    echo "Zeroing out $devname..."
    dd if=/dev/zero of="$devname" bs=1k count="$size_kb"
    if [ $? -ne 0 ]; then
        echo "Failed to zero out $devname."
        return 1
    fi

    # Create the JFS file system
    echo "Creating JFS file system on $devname..."
    mkfs.jfs -f "$devname"
    if [ $? -ne 0 ]; then
        echo "Failed to create JFS file system on $devname."
        return 1
    fi

    echo "Successfully set up JFS file system on $devname."
    return 0
}

loadmods
populate_mountpoint
check_device "$devname" "$size_kb"
setup_jfs