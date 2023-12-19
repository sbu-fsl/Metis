#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Pei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

pkill -9 -f "./mcfs-main.pml"
pkill -9 -f "./mcfs-main.pml.swarm"
pkill -9 -f "sh ./script"
pkill -9 -f "./pan"
umount /dev/ram*
umount /dev/mtdblock*
umount /mnt/test-*
