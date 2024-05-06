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

# This script should be placed in fs-state/mcfs_scripts folder

EXT4_SZKB=256
TESTFS_SZKB=51200 # 50 MiB

cd ..
sudo ./stop.sh

cd ../kernel/brd-for-$(uname -r)/
sudo rmmod brd
sudo rmmod testFS
make -C /lib/modules/$(uname -r)/build M=$(pwd)
sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$TESTFS_SZKB
cd ../../fs-state/
sudo ./setup.sh -f ext4:$EXT4_SZKB:testFS:$TESTFS_SZKB

