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

# This script should be placed in fs-state/mcfs_scripts folder

# If we run MCFS ext4 vs. btrfs with fallocate, we need to increase the
# size of ext4 device from 256 KiB to 2 MiB; otherwise, we will get ENOSPC
# for ext4 on fallocate operation.

EXT4_SZKB=2048 # 2 MiB
BTRFS_SZKB=16384 # 16 MiB

cd ..
sudo ./stop.sh

cd ../kernel/brd-for-5.19.7
sudo rmmod brd
make -C /lib/modules/$(uname -r)/build M=$(pwd)
sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$BTRFS_SZKB
cd ../../fs-state/
sudo ./setup.sh -f ext4:$EXT4_SZKB:btrfs:$BTRFS_SZKB
