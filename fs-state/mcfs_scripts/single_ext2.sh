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

EXT4_SZKB=256
EXT2_SZKB=256 

cd ..
sudo ./stop.sh
sudo rmmod brd

# If Ext4 has the same size as Ext2
if [ "$EXT4_SZKB" -eq "$EXT2_SZKB" ]; then
    ./loadmods.sh
else
    cd ../kernel/brd-for-$(uname -r)
    make -C /lib/modules/$(uname -r)/build M=$(pwd)
    sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$EXT2_SZKB
    cd ../../fs-state/
fi

sudo ./setup.sh -f ext4:$EXT4_SZKB:ext2:$EXT2_SZKB
