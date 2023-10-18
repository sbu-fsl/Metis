#!/bin/bash

# set -x
# trap read debug

MNTPNT="/mnt/test-nilfs2"
BRD_DIR="/mcfs/jfs-mcfs-2023-0427/nfs4mc/kernel/brd-for-6.3.0"
IMGFILE_DIR="/mcfs/jfs-mcfs-2023-0427/nfs4mc/reproduce_oops"
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
