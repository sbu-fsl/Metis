#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Divyaank Tiwari
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# Replayer command to execute
command="sudo ./replay"

# Number of execution iterations
num_executions=100

# Single log file for all executions
log_file="loop_replay.log"

for ((i = 0; i < num_executions; i++)); do
    echo "Replay iteration: $((i+1))" | tee -a "$log_file"

    # Execute the command and display output only on the console
    $command 2>&1

    # sleep (duration in secs) before next execution
    sleep 2
done
