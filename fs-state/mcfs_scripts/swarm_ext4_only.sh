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
# Make sure the swarm.lib is set up (esp. cpus)

NUMVT=32

EXT4_SZKB=256

cd ..
sudo ./stop.sh
sudo rmmod brd

./loadmods.sh

./setup_swarm.sh -f ext4:$EXT4_SZKB -n $NUMVT
