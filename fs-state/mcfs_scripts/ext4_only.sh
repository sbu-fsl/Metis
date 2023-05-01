#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder

EXT4_SZKB=256

cd ..
sudo ./stop.sh
sudo rmmod brd

modprobe brd rd_nr=1 rd_size=$EXT4_SZKB

sudo ./setup.sh -f ext4:$EXT4_SZKB
