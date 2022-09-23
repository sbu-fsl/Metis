#!/bin/bash

# Ext4 parameters
EXT4_SIZE=256 # in KiB for ramdisk
EXT4_MNT_DIR="/mnt/test-ext4"
EXT4_DEVICE="/dev/ram0"

# VeriFS2 parameters
VERIFS2_MNT_DIR="/mnt/test-verifs2"

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

setup_verifs2() {
    if test -n "$(mount | grep $VERIFS2_MNT_DIR)" ; then
        umount $VERIFS2_MNT_DIR || exit $?
    fi

    if test -d $VERIFS2_MNT_DIR ; then
        rm -rf $VERIFS2_MNT_DIR
    fi
    mkdir -p $VERIFS2_MNT_DIR

    mount -t fuse.fuse-cpp-ramfs verifs2 $VERIFS2_MNT_DIR
}

FSNAME=$1

setup_$FSNAME

if [ $FSNAME == "ext4" ]; then
    ./syscall_seqs $FSNAME $EXT4_MNT_DIR $EXT4_DEVICE
elif [ $FSNAME == "verifs2" ]; then
    ./syscall_seqs $FSNAME $VERIFS2_MNT_DIR
else
    echo "[Error] file system not supported"
    echo "Usage: $0 <fs-name>"
    exit -1
fi
