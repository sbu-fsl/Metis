#!/bin/bash

JFFS2_TMP_IMG_DIR="/tmp/temp_image_dir"
JFFS2_IMG="/tmp/jffs2.img"
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"
MTD_DEVICE="/dev/mtd0"
JFFS2_TEST_FILE="$JFFS2_MNT_DIR/test.txt"

setup() {
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

    mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR || exit $?
}

setup

echo "writing 16 bytes (all 1s) from start"
./write_file $JFFS2_TEST_FILE 0 16 1
hexdump -C -v $JFFS2_TEST_FILE

echo "truncating file to 8 bytes"
truncate -s 8 $JFFS2_TEST_FILE
hexdump -C -v $JFFS2_TEST_FILE

echo "writing 4 bytes (all 2s) from offset 20"
./write_file $JFFS2_TEST_FILE 20 4 2

hexdump -C -v $JFFS2_TEST_FILE

echo "dropping all caches"
echo 3 > /proc/sys/vm/drop_caches

echo "the correct file should be 8 x 1s, then 12 x 0s, then 4 x 2s"
echo "the INcorrect file has 16 x 1s, then 4 x 0s, then 4 x 2s"
hexdump -C -v $JFFS2_TEST_FILE
