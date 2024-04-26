#!/bin/bash

# 256 KiB, 16 MiB (16384)
NFS_GANESHA_EXT4_SZKB=16384

cd ..
sudo ./stop.sh
sudo rmmod brd

modprobe brd rd_nr=1 rd_size=$NFS_GANESHA_EXT4_SZKB

sudo ./setup.sh -f nfs-ganesha-ext4:$NFS_GANESHA_EXT4_SZKB
