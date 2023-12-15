#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

SERVER=sgdp05
FSCHECKER=mcfs
SUFFIX="Depth100Ext4Journal5mins"

KERNEL_EXT4_SRC="/sys/kernel/debug/gcov/mcfs/Linux_Kernel_Install/linux-6.0.6/fs/ext4"
# 8192 - 8 MiB device for ext4 AUTO enables journaling (doesn't work: 4/5/6/7 MiB)
# sudo dumpe2fs /dev/ram0 | grep has_journal: check if ext4 journaling enabled
EXT4_SZKB=8192
CURDIR=$PWD
OUTPUT_INFO="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_ext4_coverage_${SUFFIX}.info"
OUTPUT_DIR="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_cov_out_${SUFFIX}"

cd ..
sudo ./stop.sh
sudo rmmod brd
# sudo ./loadmods.sh

modprobe brd rd_nr=1 rd_size=$EXT4_SZKB
sudo lcov --zerocounters

start=`date +%s`
./setup.sh -f ext4:$EXT4_SZKB
end=`date +%s`
runtime=$((end-start))

lcov --capture --directory $KERNEL_EXT4_SRC --rc lcov_branch_coverage=1 --output-file $OUTPUT_INFO
genhtml $OUTPUT_INFO --rc genhtml_branch_coverage=1 --output-directory $OUTPUT_DIR

echo "Total Ext4 MCFS Tests Runtime: " $runtime
