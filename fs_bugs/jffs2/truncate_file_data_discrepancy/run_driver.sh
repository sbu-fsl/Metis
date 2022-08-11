#!/bin/bash

DRIVER_LOOP_MAX=100000
FILENAME="test.txt"
TRUNCATE_SIZE=59752

# ext4 parameters
EXT4_SIZE=256 # in KiB for ramdisk
EXT4_MNT_DIR="/mnt/test-ext4-truncate"
EXT4_DEVICE="/dev/ram0"
EXT4_REPLAY_IMG="./after_checkpoint_images/ext4-dev-3846.img"

# jffs2 parameters
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2-truncate"
MTDBLK_DEVICE="/dev/mtdblock0"
JFFS2_REPLAY_IMG="./after_checkpoint_images/jffs2-dev-3846.img"

EXT4_FILE="$EXT4_MNT_DIR/$FILENAME"
JFFS2_FILE="$JFFS2_MNT_DIR/$FILENAME"

setup_jffs2() {
    modprobe mtd
    modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024) erase_size=16
    modprobe mtdblock

    if test -n "$(mount | grep $JFFS2_MNT_DIR)" ; then
        umount $JFFS2_MNT_DIR || exit $?
    fi

    if test -d $JFFS2_MNT_DIR ; then
        rm -rf $JFFS2_MNT_DIR
    fi
    mkdir -p $JFFS2_MNT_DIR

    dd if=$JFFS2_REPLAY_IMG of=$MTDBLK_DEVICE &> /dev/null || exit $?
    mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR || exit $?
}

setup_ext4() {
    modprobe brd rd_nr=1 rd_size=$EXT4_SIZE

    if test -n "$(mount | grep $EXT4_MNT_DIR)" ; then
        umount $EXT4_MNT_DIR || exit $?
    fi

    if test -d $EXT4_MNT_DIR ; then
        rm -rf $EXT4_MNT_DIR
    fi
    mkdir -p $EXT4_MNT_DIR

    dd if=$EXT4_REPLAY_IMG of=$EXT4_DEVICE &> /dev/null || exit $?
    mount -t ext4 $EXT4_DEVICE $EXT4_MNT_DIR || exit $?
}

COUNTER=0
while [  $COUNTER -lt $DRIVER_LOOP_MAX ]; do
    echo "Current: $COUNTER out of $DRIVER_LOOP_MAX"
    setup_jffs2
    setup_ext4
    if [ ! -f $EXT4_FILE ] || [ ! -f $JFFS2_FILE ]
    then 
        echo "SKIPPED"
        let COUNTER=COUNTER+1 
        continue
    fi
    truncate -s $(($TRUNCATE_SIZE+$COUNTER*13)) $EXT4_FILE
    truncate -s $(($TRUNCATE_SIZE+$COUNTER*13)) $JFFS2_FILE

    DIFF=$(diff <(hexdump $EXT4_FILE) <(hexdump $JFFS2_FILE))
    if [ "$DIFF" != "" ] 
    then
        echo "JFFS2 TRUNCATE BUG REPRODUCED!"
        echo $DIFF
        exit -1
    fi
    let COUNTER=COUNTER+1 
done
exit 0
