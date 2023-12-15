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

make min_repro

# Parse file systems
# SET THESE VARIABLE BELOW
FSALL="ext4:jfs"
IMGSUFFIX="state-3219-seq-4727576-ckpt-0.img"
LOGDIR="./Ext4-JFS-sgdp02-20230427-190024-1249063"
SEQFILE="sequence-pan-20230427-190024-1249063.log"
DEVSIZE="256:16384"
# Devices with desired sizes should be already created before running this script
DEVALL="/dev/ram0:/dev/ram1"
# Note that the mountpoints are auto allocated, note here for reference
MPALL="/mnt/test-ext4-i0-s0:/mnt/test-jfs-i1-s0"

FS1=$(echo $FSALL | cut -d: -f1)
FS2=$(echo $FSALL | cut -d: -f2)

IMGFILE1="cbuf-$FS1-$IMGSUFFIX"
IMGFILE2="cbuf-$FS2-$IMGSUFFIX"

# SEQLOG="sequence.log"
SEQLOG="$LOGDIR/$SEQFILE"
IMGALL="$LOGDIR/$IMGFILE1:$LOGDIR/$IMGFILE2"

# Parse arguments
DEVSZ1=$(echo $DEVSIZE | cut -d: -f1)
DEVSZ2=$(echo $DEVSIZE | cut -d: -f2)

DEV1=$(echo $DEVALL | cut -d: -f1)
DEV2=$(echo $DEVALL | cut -d: -f2)

IMG1=$(echo $IMGALL | cut -d: -f1)
IMG2=$(echo $IMGALL | cut -d: -f2)

MP1=$(echo $MPALL | cut -d: -f1)
MP2=$(echo $MPALL | cut -d: -f2)

# Unmount relevant devices
if test -n "$(mount | grep $DEV1)" ; then
    umount $DEV1 || exit $?
fi

if test -n "$(mount | grep $DEV2)" ; then
    umount $DEV2 || exit $?
fi

# Unmount relevant mountpoints
if test -n "$(mount | grep $MP1)" ; then
    umount $MP1 || exit $?
fi

if test -n "$(mount | grep $MP2)" ; then
    umount $MP2 || exit $?
fi

# Copy devices
# dd if=$IMG1 of=./$DEV1 bs=4k status=none
# dd if=$IMG2 of=./$DEV2 bs=4k status=none

# Mount file systems 
# mount $DEV1 $MP1 || exit $?
# mount $DEV2 $MP2 || exit $?

# Usage: ./reproducer -K 0:$FS1:$DEVSZ1:$FS2:$DEVSZ2 seqlog img1 img2 dev1 dev2
./min_repro -K 0:$FS1:$DEVSZ1:$FS2:$DEVSZ2 $SEQLOG $IMG1 $IMG2 $DEV1 $DEV2
