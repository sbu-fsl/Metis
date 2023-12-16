#!/bin/bash

# Default Ext4: 256 KiB
EXT4_SZKB=256

cd ..
# Stop MCFS and unmount all test file systems
sudo ./stop.sh

sudo rmmod brd

modprobe brd rd_nr=1 rd_size=$EXT4_SZKB

# Start MCFS
./setup.sh -f ext4:$EXT4_SZKB
