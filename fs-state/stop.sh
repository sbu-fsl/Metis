#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Pei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
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
