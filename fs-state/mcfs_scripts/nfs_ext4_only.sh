#!/bin/bash

# 256 KiB or 16 MiB (16384)
NFS_EXT4_SZKB=256

cd ..
sudo ./stop.sh
sudo rmmod brd

modprobe brd rd_nr=1 rd_size=$NFS_EXT4_SZKB

sudo ./setup.sh -f nfs-ext4:$NFS_EXT4_SZKB
