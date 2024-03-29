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

# Initialize the sums to zero
SUMSECOND=0
SUMOPS=0
SUMSTATES=0

FILEPTRN="perf-*.csv"

# 1. grep all the perf-*.csv files
for file in $FILEPTRN; do
    # 2. for each csv file, get the last line 
    last_line=$(tail -n 1 $file)

    # 3. For each last line, split this line by "," and get the first and second value
    DURSECONDS=$(echo $last_line | cut -d',' -f1)
    OPS=$(echo $last_line | cut -d',' -f2)
    STATES=$(echo $last_line | cut -d',' -f3)
    # echo "DURSECONDS: $DURSECONDS"
    # echo "OPS: $OPS"
    # echo "STATES: $STATES"
    # 4. Sum every first values and Sum every second values
    SUMSECOND=$(echo "$SUMSECOND + $DURSECONDS" | bc -l)
    SUMOPS=$(echo "$SUMOPS + $OPS" | bc -l)
    SUMSTATES=$(echo "$SUMSTATES + $STATES" | bc -l)
done

echo "Total of duration seconds: $SUMSECOND"
echo "Total number of operations: $SUMOPS"
echo "Total number of states: $SUMSTATES"
