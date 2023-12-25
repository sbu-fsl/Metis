#!/bin/bash

FS_STATE_DIR="../fs-state"

cd $FS_STATE_DIR
./stop.sh 
make clean

sudo rmmod mtdblock
sudo rmmod mtdram 
sudo rmmod mtd_blkdevs
sudo rmmod brd

./loadmods.sh

sudo ./setup.sh -f ext4:256:jffs2:256
