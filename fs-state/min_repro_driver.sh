#!/bin/bash

make min_repro

# SEQLOG="sequence-pan-20230407-183853-171036.log"
SEQLOG="sequence.log"
FSALL="ext4:jfs"
DEVSIZE="256:16384"
# Devices with desired sizes should be already created before running this script
DEVALL="/dev/ram0:/dev/ram1"
IMGALL="cbuf-ext4-state-3224-seq-4837094-ckpt-0.img:cbuf-jfs-state-3224-seq-4837094-ckpt-0.img"

# Parse arguments
FS1=$(echo $FSALL | cut -d: -f1)
FS2=$(echo $FSALL | cut -d: -f2)

DEVSZ1=$(echo $DEVSIZE | cut -d: -f1)
DEVSZ2=$(echo $DEVSIZE | cut -d: -f2)

DEV1=$(echo $DEVALL | cut -d: -f1)
DEV2=$(echo $DEVALL | cut -d: -f2)

IMG1=$(echo $IMGALL | cut -d: -f1)
IMG2=$(echo $IMGALL | cut -d: -f2)

# Copy devices
dd if=$DEV1 of=./$IMG1 bs=4k status=none
dd if=$DEV2 of=./$IMG2 bs=4k status=none

# Usage: ./reproducer seqlog fs1 fs2 mp1 mp2 dev1 dev2 
./min_repro -K 0:$FS1:$DEVSZ1:$FS2:$DEVSZ2 $SEQLOG
