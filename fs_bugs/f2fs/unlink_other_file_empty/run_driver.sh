#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

DRIVER_LOOP_MAX=1000000

F2FS_MNT_DIR="/mnt/test-f2fs-i1-s0"
F2FS_RAMDISK_DEV="/dev/ram1"

if test -n "$(mount | grep $F2FS_RAMDISK_DEV)" ; then
    umount $F2FS_RAMDISK_DEV || exit $?
fi

if test -n "$(mount | grep $F2FS_MNT_DIR)" ; then
    umount $F2FS_MNT_DIR || exit $?
fi

if test -d $F2FS_MNT_DIR ; then
    rm -rf $F2FS_MNT_DIR
fi
mkdir -p $F2FS_MNT_DIR

./driver $F2FS_MNT_DIR $F2FS_RAMDISK_DEV ./cbuf-f2fs-state-2851-seq-9245862-ckpt-0.img $DRIVER_LOOP_MAX
