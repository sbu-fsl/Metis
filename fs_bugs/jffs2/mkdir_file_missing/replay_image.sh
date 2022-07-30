#!/bin/bash

DRIVER_LOOP_MAX=10000

# jffs2 parameters
JFFS2_TMP_IMG_DIR="/tmp/temp_image_dir"
JFFS2_IMG="/tmp/jffs2.img"
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"
REPLAY_IMAGE="$1"

if [ -z "$REPLAY_IMAGE" ]; then
    echo "Usage: $0 <jffs2-image-path>"
    exit -1
fi

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

    if test -d $JFFS2_TMP_IMG_DIR ; then
        rm -rf $JFFS2_TMP_IMG_DIR
    fi
    mkdir -p $JFFS2_TMP_IMG_DIR || exit $?
    dd if=$REPLAY_IMAGE of=$MTDBLK_DEVICE || exit $?
    # mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR || exit $?
}

setup_jffs2

# Loop: mount image, run driver, unmount image
COUNTER=0
while [  $COUNTER -lt $DRIVER_LOOP_MAX ]; do
    echo "counter $COUNTER of $DRIVER_LOOP_MAX"
    ./driver $JFFS2_MNT_DIR $MTDBLK_DEVICE jffs2 1
    dd if=$REPLAY_IMAGE of=$MTDBLK_DEVICE || exit $?
    let COUNTER=COUNTER+1 
done
