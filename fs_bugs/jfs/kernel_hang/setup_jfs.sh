#!/bin/bash

# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2023-2024 Divyaank Tiwari
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache
# License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# Mount directory for JFS 
mntpoint="/mnt/test-jfs-i0-s0"

# Backing ramdisk for JFS
ram_device="/dev/ram0"

# Backing loop device for JFS
loop_device="$(sudo losetup -f)"

# Backing (zeroed-out) image file which is required by the loop device
img_file="./loopfile.img"

# Size of the ramdisk
size_kb=$((16 * 1024))

# Function to install jfsutils, which is required for mkfs.jfs
install_jfsutils() {
    # Check if jfsutils is already installed
    if command -v fsck.jfs >/dev/null 2>&1; then
        echo "jfsutils is already installed."
        return 0
    fi

    # Determine the package manager and install jfsutils accordingly
    if command -v apt-get >/dev/null 2>&1; then
        echo "Detected apt-get. Installing jfsutils..."
        sudo apt-get update
        sudo apt-get install -y jfsutils
    elif command -v yum >/dev/null 2>&1; then
        echo "Detected yum. Installing jfsutils..."
        sudo yum install -y jfsutils
    elif command -v dnf >/dev/null 2>&1; then
        echo "Detected dnf. Installing jfsutils..."
        sudo dnf install -y jfsutils
    elif command -v pacman >/dev/null 2>&1; then
        echo "Detected pacman. Installing jfsutils..."
        sudo pacman -S jfsutils
    else
        echo "No known package manager found. Please install jfsutils manually."
        return 1
    fi

    echo "jfsutils installation completed."
}

# This function checks the status of the loop device and prepares it for setup
check_loopdev() {
    # Check if the loop device is in use and detach if necessary
    if losetup -a | grep -q "$loop_device"; then
        echo "$loop_device is already in use. Detaching..."
        sudo losetup -d "$loop_device"
        if [ $? -ne 0 ]; then
            echo "Failed to detach loop device: $loop_device"
            exit 1
        fi
    fi

    # Check if the loop device is mounted and unmount if necessary
    if mount | grep -q "$loop_device"; then
        echo "$loop_device is mounted. Unmounting..."
        sudo umount "$loop_device"
        if [ $? -ne 0 ]; then
            echo "Failed to unmount loop device: $loop_device"
            exit 1
        fi
    fi
}

# This function sets up the loop device through the losetup command
setup_loopdev() {
    # Set up the loop device
    echo "Setting up the loop device: $loop_device"
    sudo losetup "$loop_device" "$img_file"
    if [ $? -ne 0 ]; then
        echo "Failed to set up loop device: $loop_device"
        exit 1
    fi
}

# Creates the ramdisk, loads brd module and checks whether the size is valid
create_ramdev() {

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
    modprobe brd rd_nr=1 rd_size=$size_kb

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

# Checks and initializes the mount folder
populate_mountpoint() {

    # Check if any file-system has been mounted on the folder
    if mount | grep -q "$mntpoint"; then
        echo "A filesystem is mounted on $mntpoint. Unmounting..."
        # Unmount the filesystem
        umount -f "$mntpoint"
        if [ $? -eq 0 ]; then
            echo "Successfully unmounted $mntpoint."
        else
            echo "Failed to unmount $mntpoint. Please check for issues."
            return 1
        fi
    else
        echo "No filesystem is mounted on $mntpoint."
    fi

    # Create the required directory
    mkdir -p "$mntpoint"
    if [ $? -eq 0 ]; then
        echo "Successfully created directory $mntpoint."
    else
        echo "Failed to create directory $mntpoint. Please check for issues."
        return 1
    fi
}

# Verifies ramdisk device size
check_ramdev() {
    # local ram_device="$1"
    # local size_kb="$2"
    local exp_size_bytes=$((size_kb * 1024))

    # Open the device (check if the file exists and is readable)
    if [ ! -r "$ram_device" ]; then
        echo "Cannot open $ram_device (err=$(strerror $?))"
        return 1
    fi

    # Get device info
    if ! stat --printf='' "$ram_device" 2>/dev/null; then
        echo "Cannot stat $ram_device (err=$(strerror $?))"
        return 1
    fi

    # Check if it's a block device
    if [ ! -b "$ram_device" ]; then
        echo "$ram_device is not a block device."
        return 1
    fi

    # Get the size of the device in bytes
    devsize=$(blockdev --getsize64 "$ram_device" 2>/dev/null)
    if [ $? -ne 0 ]; then
        echo "Cannot get size of $ram_device (err=$(strerror $?))"
        return 1
    fi

    # Check if the device size is smaller than expected
    if [ "$devsize" -lt "$exp_size_bytes" ]; then
        echo "$ram_device is smaller than expected (expected ${size_kb} KB, got $((devsize / 1024)) KB)."
        return 1
    fi

    return 0
}

# This function orchestrates the creation of JFS file system on a loop device (/dev/loop*)
setup_jfs_on_loopdev() {
    # Create the backing file
    echo "Creating backing file..."
    dd if=/dev/zero of="$img_file" bs=1K count="$size_kb"
    if [ $? -ne 0 ]; then
        echo "Failed to create image file: $img_file"
        exit 1
    fi

    check_loopdev
    setup_loopdev

    # Zero out the loop device (optional but recommended)
    echo "Zeroing out the loop device: $loop_device"
    dd if=/dev/zero of="$loop_device" bs=1K count="$size_kb"
    if [ $? -ne 0 ]; then
        echo "Failed to zero out loop device: $loop_device"
        sudo losetup -d "$loop_device"
        exit 1
    fi

    # Create the JFS filesystem
    echo "Creating JFS filesystem on the loop device: $loop_device"
    sudo mkfs.jfs -f "$loop_device"
    if [ $? -ne 0 ]; then
        echo "Failed to create JFS filesystem on: $loop_device"
        sudo losetup -d "$loop_device"
        exit 1
    fi

    echo "Successfully set up JFS filesystem on $loop_device"
}

# This function orchestrates the creation of JFS file system on a ram device (/dev/ram*)
setup_jfs_on_ramdev() {
    create_ramdev
    populate_mountpoint
    check_ramdev

    # Zero out the device
    echo "Zeroing out $ram_device..."
    dd if=/dev/zero of="$ram_device" bs=1k count="$size_kb"
    if [ $? -ne 0 ]; then
        echo "Failed to zero out $ram_device."
        return 1
    fi

    # Create the JFS file system
    echo "Creating JFS file system on $ram_device..."
    mkfs.jfs -f "$ram_device"
    if [ $? -ne 0 ]; then
        echo "Failed to create JFS file system on $ram_device."
        return 1
    fi

    echo "Successfully set up JFS file system on $ram_device."
    return 0
}

######################################################################
### NOW ACTUALLY SETUP JFS

# First install jfsutils
install_jfsutils

# To setup JFS on /dev/ram*
setup_jfs_on_ramdev

# To setup JFS on /dev/loop*
# setup_jfs_on_loopdev
