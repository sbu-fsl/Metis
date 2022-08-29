#!/bin/bash

DRIVER_LOOP_MAX=1000000
# Test 1: buggy point
# EXT4_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/buggy_discrepancy_point_images/ext4-dev-seq-27395772.img"
# JFFS2_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/buggy_discrepancy_point_images/jffs2-dev-seq-27395772.img"

# Test 2: Latest checkpoint 3845
# EXT4_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/after-checkpoint/ext4-dev-3845.img"
# JFFS2_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/after-checkpoint/jffs2-dev-3845.img"

# Test 3: Latest checkpoint 3844
EXT4_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/after-checkpoint/ext4-dev-3844.img"
JFFS2_IMAGE="/mcfs/replay-mkdir-bug-2022-0726/nfs-validator/fs-state/dumped_images_for_unlink_before_discrepancy_issue_20220828/after-checkpoint/jffs2-dev-3844.img"

EXT4_DEV="/dev/ram0"
JFFS2_DEV="/dev/mtdblock0"

EXT4_MP="/mnt/test-ext4-before-unlink"
JFFS2_MP="/mnt/test-jffs2-before-unlink"

EXT4_TEST_FILE="$EXT4_MP/test.txt"
JFFS2_TEST_FILE="$JFFS2_MP/test.txt"

COUNTER=0
while [  $COUNTER -lt $DRIVER_LOOP_MAX ]; do
    echo "Current counter: $COUNTER"
    if [ "$(mount | grep $EXT4_MP)" ]; then
        umount -f $EXT4_MP
    fi

    if [ "$(mount | grep $JFFS2_MP)" ]; then
        umount -f $JFFS2_MP
    fi

    dd if=$EXT4_IMAGE of=$EXT4_DEV &> /dev/null
    dd if=$JFFS2_IMAGE of=$JFFS2_DEV &> /dev/null

    mount -t ext4 $EXT4_DEV $EXT4_MP
    mount -t jffs2 $JFFS2_DEV $JFFS2_MP

    DIFF=$(diff <(hexdump $EXT4_TEST_FILE) <(hexdump $JFFS2_TEST_FILE))
    if [ "$DIFF" != "" ] 
    then
        echo "JFFS2 BEFORE UNLINK BUG REPRODUCED (before driver)!"
        echo $DIFF
        exit -1
    fi

    ./driver $EXT4_TEST_FILE 57344 1021 149 $EXT4_MP $EXT4_DEV ext4
    ./driver $JFFS2_TEST_FILE 57344 1021 149 $JFFS2_MP $JFFS2_DEV jffs2

    DIFF=$(diff <(hexdump $EXT4_TEST_FILE) <(hexdump $JFFS2_TEST_FILE))
    if [ "$DIFF" != "" ] 
    then
        echo "JFFS2 BEFORE UNLINK BUG REPRODUCED (after driver)!"
        echo $DIFF
        exit -1
    fi
    umount -f $EXT4_MP
    umount -f $JFFS2_MP

    let COUNTER=COUNTER+1 
done
