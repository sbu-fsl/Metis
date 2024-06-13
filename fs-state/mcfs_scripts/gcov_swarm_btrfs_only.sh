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

SERVER=sgdp05
FSCHECKER=mcfs
FSTYPE=btrfs
SUFFIX="6VTsMix60mins"
NUM_VTS=6
DURATION=60m
DEVSZKB=16384

KERNEL_GCOV_SRC="/sys/kernel/debug/gcov/mcfs/Linux_Kernel_Install/linux-6.0.6/fs/$FSTYPE"

CURDIR=$PWD
OUTPUT_INFO="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_${FSTYPE}_coverage_${SUFFIX}.info"
OUTPUT_DIR="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_cov_out_${SUFFIX}"

cd ..
sudo ./stop.sh
sudo rmmod brd

modprobe brd rd_nr=$NUM_VTS rd_size=$DEVSZKB

# Remember to edit swarm.lib before running MCFS

sudo lcov --zerocounters
start=`date +%s`

./setup_swarm.sh -f $FSTYPE:$DEVSZKB -n $NUM_VTS &
sleep $DURATION && ./stop.sh

end=`date +%s`
runtime=$((end-start))

lcov --capture --directory $KERNEL_GCOV_SRC --rc lcov_branch_coverage=1 --output-file $OUTPUT_INFO
genhtml $OUTPUT_INFO --rc genhtml_branch_coverage=1 --output-directory $OUTPUT_DIR

echo "Total Tests Runtime ($SUFFIX): " $runtime
