#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Ajay Hegde
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# Standalong code coverage script

#Git clone Crash Monkey from: https://github.com/utsaslab/crashmonkey
#Copy this script inside Cloned CrashMonkey folder

#Usage: ./crashmonkey_coverage.sh <file_system>
# eg. ./crashmonkey_coverage.sh ext4

#echo $reset_cc_data
if [ -d "ext4_op" ]; then
    echo "Removing existing Gcov output dir"
    sudo rm -rf ext4_op
fi

if [ -f "main_coverage.info" ]; then
    echo "Removing existing main coverage info file"
    sudo rm main_coverage.info
fi

echo "Resetting Coverage Kernel counters and running CrashMonkey Ext4 Test"

#reset_cc_data =
sudo lcov --zerocounters

#time source 
start=`date +%s`
python3 xfsMonkey.py -f /dev/sda -d /dev/cow_ram0 -t $1 -e 102400 -u /build/tests/seq1/ > outfile
end=`date +%s`
runtime=$((end-start))

#lcov_collect = 
sudo lcov --capture --output-file kernel_latest.info --gcov-tool /usr/bin/gcov-7 

echo "Total CrashMonkey Tests Runtime: " $runtime

#echo $lcov_collect
#generate_coverage_info = 
sudo genhtml kernel_latest.info --output-directory ext4_op
#echo $generate_coverage_info

