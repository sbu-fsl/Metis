#!/bin/bash

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
