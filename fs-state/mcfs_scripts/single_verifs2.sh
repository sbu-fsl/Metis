#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder
# Make sure that VeriFS2 is installed

EXT4_SZKB=256
VERIFS2_SZKB=0 

cd ..
sudo ./stop.sh
sudo rmmod brd

./loadmods.sh

sudo ./setup.sh -f ext4:$EXT4_SZKB:verifs2:$VERIFS2_SZKB
