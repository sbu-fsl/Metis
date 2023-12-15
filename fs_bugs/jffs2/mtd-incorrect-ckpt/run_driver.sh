#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

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
