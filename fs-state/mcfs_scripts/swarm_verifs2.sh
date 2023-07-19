#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder

# This script is for the Swarm verification master node
# Make sure the swarm.lib is set up
# Make sure that VeriFS2 is installed

NUMVT=6

EXT4_SZKB=256
VERIFS2_SZKB=0 

cd ..
sudo ./stop.sh
sudo rmmod brd

./loadmods.sh

./setup_swarm.sh -f ext4:$EXT4_SZKB:verifs2:$VERIFS2_SZKB -n $NUMVT
