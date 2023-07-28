#!/bin/bash

# Default Ext4: 2 MiB
EXT4_SZMB=2
EXT4_SZKB=$(expr 1024 \* $EXT4_SZMB)

cd ..
# Stop MCFS and unmount all test file systems
sudo ./stop.sh

sudo rmmod brd
modprobe brd rd_nr=1 rd_size=$EXT4_SZKB

# Start MCFS
./setup.sh -f ext4:$EXT4_SZKB
