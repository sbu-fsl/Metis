#!/bin/bash
 
# Replayer setup script for EXT4 vs JFS
 
EXT4_SZKB=256
JFS_SZKB=16384 # 16 MiB

cd ../kernel/brd-for-6.6.1
sudo rmmod brd
make -C /lib/modules/$(uname -r)/build M=$(pwd)
sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$JFS_SZKB