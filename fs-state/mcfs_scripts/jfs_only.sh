#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder

JFS_SZKB=16384 # 16 MiB

cd ..
sudo ./stop.sh
sudo rmmod brd

modprobe brd rd_nr=1 rd_size=$JFS_SZKB

sudo ./setup.sh -f jfs:$JFS_SZKB
