#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# Usage: ./only_one_fs_iocov_lttng.sh -f <file system name> -t <time to sleep in seconds> -e <experiment config>
# Example: ./only_one_fs_iocov_lttng.sh -f ext4 -t 3600 -e "with-iocov"

CURDIR=$(pwd)

FSSZKB=0

# Supported File Systems: ext4, verifs2, btrfs, jfs
EXT4_SZKB=2048 # 2 MiB minimum size for comparing, 256KiB for one file system only
# Ensure VeriFS2 is installed
VERIFS2_SZKB=0
# Ensure VeriFS1 is installed
VERIFS1_SZKB=0
EXT2_SZKB=2048
BTRFS_SZKB=16384 # 16 MiB
XFS_SZKB=16384 # 16 MiB
JFS_SZKB=16384 # 16 MiB
NILFS2_SZKB=1028 # 1028 KiB

FSTYPE="ext4"
DURATION_SECS="3600"
EXPCONFIG="unknown-expconfig"
TIMESTAMP="unknown-timestamp"

while [[ $# -gt 0 ]]; do
    key=$1;
    case $key in
        -f|--fs)
            FSTYPE="$2"
            shift
            shift
            ;;
        -d|--duration)
            DURATION_SECS="$2"
            shift
            shift
            ;;
        -e|--expconfig)
            EXPCONFIG="$2"
            shift
            shift
            ;;
        -t|--timestamp)
            TIMESTAMP="$2"
            shift
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

# If fs is Ext4
if [ "$FSTYPE" == "ext4" ]; then
    FSSZKB=$EXT4_SZKB
elif [ "$FSTYPE" == "verifs2" ]; then
    FSSZKB=$VERIFS2_SZKB
elif [ "$FSTYPE" == "verifs1" ]; then
    FSSZKB=$VERIFS1_SZKB
elif [ "$FSTYPE" == "ext2" ]; then
    FSSZKB=$EXT2_SZKB
elif [ "$FSTYPE" == "xfs" ]; then
    FSSZKB=$XFS_SZKB
elif [ "$FSTYPE" == "btrfs" ]; then
    FSSZKB=$BTRFS_SZKB
elif [ "$FSTYPE" == "jfs" ]; then
    FSSZKB=$JFS_SZKB
elif [ "$FSTYPE" == "nilfs2" ]; then
    FSSZKB=$NILFS2_SZKB
else
    echo "Error: File system $1 is not supported."
    exit 1
fi

cd ..

# Stop MCFS and unmount all test file systems
sudo ./stop.sh

# Remove existing brd module and load brd module with specified size
if [ "$FSSZKB" != 0 ]; then
    sudo rmmod brd
    modprobe brd rd_nr=1 rd_size=$FSSZKB
fi

./setup.sh -f $FSTYPE:$FSSZKB &

# Wait for duration time
sleep $DURATION_SECS
./stop.sh
sudo umount -f /dev/ram0 
rmmod brd

cd $CURDIR
