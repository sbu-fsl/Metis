#!/bin/bash

# only_fs.sh run MCFS with one file system only, so it does not test 
# file system (no reference file system)
#
# only_fs.sh uses vanilla brd and does not need brd2 (../../kernel/brd*) 
# 
# This script should be placed in fs-state/mcfs_scripts folder

# Supported File Systems: ext4, verifs2, btrfs, jfs
EXT4_SZKB=256 # 256 KiB
VERIFS2_SZKB=0
BTRFS_SZKB=16384 # 16 MiB
JFS_SZKB=16384 # 16 MiB

FSNAME=$1
FSSZKB=0

if [ -z "$1" ]; then
    echo "Error: File system name is missing."
    exit 1
fi

# If fs is Ext4
if [ "$FSNAME" == "ext4" ]; then
    FSSZKB=$EXT4_SZKB
elif [ "$FSNAME" == "verifs2" ]; then
    FSSZKB=$VERIFS2_SZKB
elif [ "$FSNAME" == "btrfs" ]; then
    FSSZKB=$BTRFS_SZKB
elif [ "$FSNAME" == "jfs" ]; then
    FSSZKB=$JFS_SZKB
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

# Run MCFS
sudo ./setup.sh -f $FSNAME:$FSSZKB
