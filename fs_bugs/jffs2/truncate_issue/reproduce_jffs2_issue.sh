#!/bin/bash

JFFS2_TMP_IMG_DIR="/tmp/temp_image_dir"
JFFS2_IMG="/tmp/jffs2.img"
JFFS2_SIZE=262144
JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"
MTD_DEVICE="/dev/mtd0"
JFFS2_TEST_FILE="$JFFS2_MNT_DIR/test.txt"

remount() {
    umount $JFFS2_MNT_DIR;
    mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR;
}

setup() {
    modprobe mtd;
    modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024) erase_size=16;
    modprobe mtdblock;

    #mtdpart add $MTD_DEVICE "partition1" 0 $JFFS2_SIZE

    if [ "$(mount | grep $JFFS2_MNT_DIR)" ]; then
        umount $JFFS2_MNT_DIR;
    fi

    if [ -d $JFFS2_MNT_DIR ]; then
        rm -rf $JFFS2_MNT_DIR;
    fi
    mkdir -p $JFFS2_MNT_DIR;

    if [ -d $JFFS2_TMP_IMG_DIR ]; then
        rm -rf $JFFS2_TMP_IMG_DIR;
    fi
    mkdir -p $JFFS2_TMP_IMG_DIR;

    mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_TMP_IMG_DIR -o $JFFS2_IMG;
    dd if=$JFFS2_IMG of=$MTDBLK_DEVICE;

    mount -t jffs2 $MTDBLK_DEVICE $JFFS2_MNT_DIR;

    touch $JFFS2_TEST_FILE;
}

setup;

md5sum $MTDBLK_DEVICE $MTD_DEVICE;

echo "writing 16 bytes from start";
./write_file $JFFS2_TEST_FILE 0 16 1;
hexdump -C -v $JFFS2_TEST_FILE;
md5sum $MTDBLK_DEVICE $MTD_DEVICE;

# truncating to 8 bytes
truncate -s 8 $JFFS2_TEST_FILE;
hexdump -C -v $JFFS2_TEST_FILE;
md5sum $MTDBLK_DEVICE $MTD_DEVICE;

# remounting jffs2
remount;
ls -l $JFFS2_TEST_FILE;

echo "writing 4 bytes from 16 offset";
./write_file $JFFS2_TEST_FILE 20 4 2;

hexdump -C -v $JFFS2_TEST_FILE;
md5sum $MTDBLK_DEVICE $MTD_DEVICE;

# dropping all caches
echo 3 > /proc/sys/vm/drop_caches
hexdump -C -v $JFFS2_TEST_FILE;
md5sum $MTDBLK_DEVICE $MTD_DEVICE;
