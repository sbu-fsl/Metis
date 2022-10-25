#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder

EXT4_SZKB=256
F2FS_SZKB=38912 # 38 MiB

cd ..
sudo ./stop.sh

cd ../kernel/brd-for-5.19.7
sudo rmmod brd
make -C /lib/modules/$(uname -r)/build M=$(pwd)
sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$F2FS_SZKB
cd ../../fs-state/
sudo ./setup.sh -f ext4:$EXT4_SZKB:f2fs:$F2FS_SZKB
