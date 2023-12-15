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

MNTPNT="/mnt/test-nilfs2"

./mount_nilfs2_img.sh $MNTPNT

# Change to the mount point directory
cd $MNTPNT

# Continuously create empty files until the device is full
COUNT=0
while true; do
    mount /dev/ram0 $MNTPNT
    FILE="file_$COUNT"
    # sleep 0.01
    touch $FILE
    let COUNT=COUNT+1
    if [ ! -f $FILE ]; then
        echo "Device is full or an error occurred."
        break
    fi
    umount $MNTPNT
done

# Unmount the NILFS2 file system
echo "Unmounting the NILFS2 file system"
sudo umount $MNTPNT
