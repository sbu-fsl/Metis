#!/bin/bash

# only_fs.sh run MCFS with one file system only, so it does not test 
# file system (no reference file system)
#
# only_fs.sh uses vanilla brd and does not need brd2 (../../kernel/brd*) 
# 
# This script should be placed in fs-state/mcfs_scripts folder

CURDIR=$(pwd)

# Supported File Systems: ext4, verifs2, btrfs, jfs
EXT4_SZKB=256 # 256 KiB
# Ensure VeriFS2 is installed
VERIFS2_SZKB=0
# Ensure VeriFS1 is installed
VERIFS1_SZKB=0
EXT2_SZKB=256
BTRFS_SZKB=16384 # 16 MiB
XFS_SZKB=16384 # 16 MiB
JFS_SZKB=16384 # 16 MiB
NILFS2_SZKB=1028 # 1028 KiB

FSNAME=$1
FSSZKB=0

# Usage: ./only_fs.sh <file system name> (e.g., ./only_fs.sh ext4 1h)
if [ -z "$1" ]; then
    echo "Error: File system name is missing."
    exit 1
fi

# If fs is Ext4
if [ "$FSNAME" == "ext4" ]; then
    FSSZKB=$EXT4_SZKB
elif [ "$FSNAME" == "verifs2" ]; then
    FSSZKB=$VERIFS2_SZKB
elif [ "$FSNAME" == "verifs1" ]; then
    FSSZKB=$VERIFS1_SZKB
elif [ "$FSNAME" == "ext2" ]; then
    FSSZKB=$EXT2_SZKB
elif [ "$FSNAME" == "xfs" ]; then
    FSSZKB=$XFS_SZKB
elif [ "$FSNAME" == "btrfs" ]; then
    FSSZKB=$BTRFS_SZKB
elif [ "$FSNAME" == "jfs" ]; then
    FSSZKB=$JFS_SZKB
elif [ "$FSNAME" == "nilfs2" ]; then
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

# If the second argument is not empty
# Run MCFS script for a specific time period
if [ -n "$2" ]; then
    timeout $2 ./setup.sh -f 0:$FSNAME:$FSSZKB
fi

# Move all the experimental logs to the new folder
NEWESTCSV=$(ls -t *.csv | head -n1)
# Time stamp of csv file
TSCSV="${NEWESTCSV:9: -4}"

NEWDIR="$CURDIR/$1-$2-$FSSZKB-$TSCSV"
mkdir -p $NEWDIR

mv *$TSCSV.log *$TSCSV.csv *$TSCSV.log.gz *.txt *.img script* $NEWDIR
