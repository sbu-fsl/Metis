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

MNTPNT="/mnt/test-nilfs2"
IMGFILE="./nilfs2-dev-88-unmount-hanging.img"

# Recompile NILFS2 kernel module
# ./recompile_nilfs2_mod.sh

# Mount an existing image to create a NILFS2 filesystem
./mount_nilfs2_img.sh $MNTPNT $IMGFILE

# Create an already-existing file to reproduce the unmount hanging bug
cd $MNTPNT/d-00
touch f-02
cd -

echo "Start Unmounting..."

# Unmounting to reproduce hanging
umount $MNTPNT

echo "Reproducer finished (not supposed to see this message due to hanging)."
