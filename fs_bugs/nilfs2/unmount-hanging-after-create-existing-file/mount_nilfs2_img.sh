#!/bin/bash

# Function to show usage
usage() {
    echo "Usage: $0 <mount_point> <image_file>"
    exit 1
}

# Check for the number of arguments
if [ "$#" -ne 2 ]; then
    echo "Error: Incorrect number of arguments."
    usage
fi

# Assign arguments to variables for better readability
MNTPNT="$1"
IMGFILE="$2"

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

dd if=$IMGFILE of=$DEVFILE bs=4k status=none

mount $DEVFILE $MNTPNT
