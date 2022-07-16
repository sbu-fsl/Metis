#!/bin/bash

DRIVER_LOOP_MAX=100000

# jffs2 parameters
JFFS2_TMP_IMG_DIR="/tmp/temp_image_dir"
JFFS2_IMG="/tmp/jffs2.img"
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"
MTD_DEVICE="/dev/mtd0"

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

    flash_erase $MTD_DEVICE 0 0
    mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_TMP_IMG_DIR -o $JFFS2_IMG || exit $?
    dd if=$JFFS2_IMG of=$MTDBLK_DEVICE || exit $?

    mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR || exit $?
}

if [ $1 == "jffs2" ]; then
    setup_jffs2
    # Compile the driver and run JFFS2 test
    # sudo ./jffs2_eio_reproducer /mnt/test-jffs2 /dev/mtdblock0 jffs2 10000 2>&1 > jffs2_reproduce.log
    ./jffs2_eio_reproducer $JFFS2_MNT_DIR $MTDBLK_DEVICE jffs2 $DRIVER_LOOP_MAX
else
    echo "[Error] file system not supported"
    echo "Usage: ./reproduce_jffs2_EIO.sh <fs-name>"
    exit -1
fi
