#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Gautam Ahuja
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# NOVA parameters
NOVA_MNT_DIR="/mnt/ramdisk"
MTDBLK_DEVICE="/dev/pmem0"

# Set up NOVA
setup_nova() {

    #Check if NOVA is mounted already, if yes unmount it
    if test -n "$(mount | grep $NOVA_MNT_DIR)" ; then
        umount $NOVA_MNT_DIR || exit $?
    fi


    #Remove mount point if not created, and create it again
    if test -d $NOVA_MNT_DIR ; then
        rm -rf $NOVA_MNT_DIR
    fi
    mkdir -p $NOVA_MNT_DIR

    modprobe nova
    #https://github.com/NVSL/linux-nova/blob/master/Documentation/filesystems/nova.txt (Steps for setting up NOVA)
}

# Run driver
setup_nova

# Usage: ./driver mountpoint
./driver $NOVA_MNT_DIR 