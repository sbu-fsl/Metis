#!/bin/bash

# NOVA parameters
SERVER_MNT_DIR="/mnt/server";
LOCAL_MNT_DIR="/mnt/local";

EXT4_RAMDISK="dev/ram1";

# Set up NOVA
setup() {
    if test -n "$(mount | grep $SERVER_MNT_DIR)" ; then
        umount $SERVER_MNT_DIR || exit $?
    fi

    if test -n "$(mount | grep $LOCAL_MNT_DIR)" ; then
        umount $LOCAL_MNT_DIR || exit $?
    fi

    # Remove mount point if not created, and create it again
    if test -d $SERVER_MNT_DIR ; then
        rm -rf $SERVER_MNT_DIR
    fi

    if test -d $LOCAL_MNT_DIR ; then
        rm -rf $LOCAL_MNT_DIR
    fi

    mkdir -p $SERVER_MNT_DIR
    mkdir -p $LOCAL_MNT_DIR
    chmod 755 $SERVER_MNT_DIR
    chmod 755 $LOCAL_MNT_DIR

    systemctl restart nfs-kernel-server

    mkfs.ext4 /dev/ram1
}


# Run driver
setup

# Usage: ./driver mountpoint
./driver $NOVA_MNT_DIR 