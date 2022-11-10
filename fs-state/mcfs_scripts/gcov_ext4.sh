#!/bin/bash

SERVER=sgdp05
FSCHECKER=mcfs

KERNEL_EXT4_SRC="/sys/kernel/debug/gcov/mcfs/Linux_Kernel_Install/linux-6.0.6/fs/ext4"
EXT4_SZKB=2048
CURDIR=$PWD

cd ..
sudo ./stop.sh
sudo rmmod brd
# sudo ./loadmods.sh

modprobe brd rd_nr=1 rd_size=$EXT4_SZKB
sudo lcov --zerocounters
./setup.sh -f ext4:$EXT4_SZKB
lcov --capture --directory $KERNEL_EXT4_SRC --rc lcov_branch_coverage=1 --output-file $CURDIR/${SERVER}_${FSCHECKER}_ext4_coverage.info
genhtml $CURDIR/${SERVER}_${FSCHECKER}_ext4_coverage.info --rc genhtml_branch_coverage=1 --output-directory $CURDIR/${SERVER}_${FSCHECKER}_cov_out
