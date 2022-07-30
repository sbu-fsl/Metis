#!/bin/bash

DRIVER_LOOP_MAX=100000

# jffs2 parameters
JFFS2_TMP_IMG_DIR="/tmp/temp_image_dir"
JFFS2_IMG="/tmp/jffs2.img"
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"

# ext4 parameters
EXT4_SIZE=256 # in KiB for ramdisk
EXT4_MNT_DIR="/mnt/test-ext4"
EXT4_DEVICE="/dev/ram0"

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

    mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_TMP_IMG_DIR -o $JFFS2_IMG || exit $?
    dd if=$JFFS2_IMG of=$MTDBLK_DEVICE || exit $?
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

    mkfs.ext4 $EXT4_DEVICE
}

if [ $1 == "jffs2" ]; then
    setup_jffs2
    # Compile the driver and run JFFS2 test
    # sudo ./driver /mnt/test-jffs2 /dev/mtdblock0 jffs2 10000 2>&1 > jffs2_reproduce.log
    ./driver $JFFS2_MNT_DIR $MTDBLK_DEVICE jffs2 $DRIVER_LOOP_MAX 2>&1 > jffs2_reproduce.log
elif [ $1 == "ext4" ]; then
    setup_ext4
    # Compile the driver and run EXT4 test
    ./driver $EXT4_MNT_DIR $EXT4_DEVICE ext4 $DRIVER_LOOP_MAX 2>&1 > ext4_reproduce.log
else
    echo "[Error] file system not supported"
    echo "Usage: $0 <fs-name>"
    exit -1
fi
