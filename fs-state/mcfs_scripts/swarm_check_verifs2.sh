#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# This script should be placed in fs-state/mcfs_scripts folder

# This script is for the Swarm verification master node
# Make sure the swarm-mcfs is installed
# Make sure the swarm.lib is set up
# Make sure the VeriFS2 is installed

# For long experiment: we can do "rm -r test-ext4-i* && rm -r test-verifs2-i*" first

# This is the number of VTs 
NUMVT=6

# EXT4_SZKB=256

EXT4_SZKB=512

VERIFS2_SZKB=0 

cd ..
sudo ./stop.sh
sudo rmmod brd

# Ext4: 256 KiB (change EXT4_SZKB)
# ./loadmods.sh

# Ext4: 512 KiB (change EXT4_SZKB)
./loadlargebrds.sh

./setup_swarm.sh -f ext4:$EXT4_SZKB:verifs2:$VERIFS2_SZKB -n $NUMVT
