#!/bin/bash

DRIVER_LOOP_MAX=100000000

JFFS2_MNT_DIR="/mnt/test-jffs2"
MTDBLK_DEVICE="/dev/mtdblock0"

if test -n "$(mount | grep $MTDBLK_DEVICE)" ; then
    umount $MTDBLK_DEVICE || exit $?
fi

if test -d $JFFS2_MNT_DIR ; then
    rm -rf $JFFS2_MNT_DIR
fi
mkdir -p $JFFS2_MNT_DIR

./driver $JFFS2_MNT_DIR $MTDBLK_DEVICE ./sgdp02-cbuf-jffs2-state-3845-seq-4861890-ckpt-7.img $DRIVER_LOOP_MAX
