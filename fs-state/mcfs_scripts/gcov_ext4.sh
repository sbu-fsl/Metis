#!/bin/bash

SERVER=sgdp05
FSCHECKER=mcfs
SUFFIX="Depth100Ext4Journal5mins"

KERNEL_EXT4_SRC="/sys/kernel/debug/gcov/mcfs/Linux_Kernel_Install/linux-6.0.6/fs/ext4"
# 8192 - 8 MiB device for ext4 AUTO enables journaling (doesn't work: 4/5/6/7 MiB)
# sudo dumpe2fs /dev/ram0 | grep has_journal: check if ext4 journaling enabled
EXT4_SZKB=8192
CURDIR=$PWD
OUTPUT_INFO="./${SERVER}_${FSCHECKER}_cov_${SUFFIX}.info"
OUTPUT_DIR="./${SERVER}_${FSCHECKER}_covout_${SUFFIX}"

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

cd -

lcov --capture --directory $KERNEL_EXT4_SRC --rc lcov_branch_coverage=1 --output-file $OUTPUT_INFO
genhtml $OUTPUT_INFO --rc genhtml_branch_coverage=1 --output-directory $OUTPUT_DIR

echo "Total $SUFFIX Tests Runtime: " $runtime
