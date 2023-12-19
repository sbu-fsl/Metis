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
