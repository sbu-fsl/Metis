#!/bin/bash

MNT_DIR="/mnt/test-verifs2"
FSNAME="verifs2"

if test -n "$(mount | grep $MNT_DIR)" ; then
    umount $MNT_DIR || exit $?
fi

if test -d $MNT_DIR ; then
    rm -rf $MNT_DIR
fi
mkdir -p $MNT_DIR

mount -t fuse.fuse-cpp-ramfs $FSNAME $MNT_DIR
./driver $MNT_DIR
