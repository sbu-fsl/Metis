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

# Function to show usage
usage() {
    echo "Usage: $0 <mount_point> [optional: image_file]"
    exit 1
}

# Check for the number of arguments
if [ $# -gt 2 ] || [ $# -lt 1 ]; then
    echo "Error: Incorrect number of arguments."
    usage
fi

# Assign arguments to variables for better readability
MNTPNT="$1"

DEVFILE="/dev/ram0"
RAMDISK_SIZE=1028

if test -n "$(mount | grep $MNTPNT)" ; then
    umount $MNTPNT
fi

if test -d $MNTPNT ; then
    rm -rf $MNTPNT
fi
mkdir -p $MNTPNT 

rmmod brd

modprobe brd rd_nr=1 rd_size=$RAMDISK_SIZE

if [ -n "$2" ]; then
    IMGFILE="$2"
    dd if=$IMGFILE of=$DEVFILE bs=4k status=none
else 
    dd if=/dev/zero of=$DEVFILE bs=$RAMDISK_SIZE count=1
    mkfs.nilfs2 -B 16 -f $DEVFILE >&2
fi

mount $DEVFILE $MNTPNT
