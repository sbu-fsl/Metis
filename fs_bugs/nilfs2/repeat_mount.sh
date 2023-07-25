#!/bin/bash

# set -x
# trap read debug

MNTPNT="/mnt/test-nilfs2"
BRD_DIR="/home/ubuntu/nfs4mc/kernel/brd-for-6.2.12"
IMGFILE_DIR="/home/ubuntu/testing/reproduce_oops"
DEVFILE="/dev/ram0"

for file in "$IMGFILE_DIR"/*; do

    if test -n "$(mount | grep $MNTPNT)" ; then
        umount $MNTPNT
    fi

    if test -d $MNTPNT ; then
        rm -rf $MNTPNT
    fi
    mkdir -p $MNTPNT

    rmmod brd

    cd $BRD_DIR
    make -C /lib/modules/$(uname -r)/build M=$(pwd)
    insmod /lib/modules/$(uname -r)/kernel/drivers/block/brd.ko rd_nr=1 rd_size=1028

    dd if=$file of=$DEVFILE bs=4k status=none

    mount $DEVFILE $MNTPNT

    echo "Finished testing $(basename "$file")"
done
