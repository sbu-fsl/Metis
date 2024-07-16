#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2023-2024 Divyaank Tiwari
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache 
# License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# Replayer command to execute
command="sudo ./replay"

# Number of execution iterations
num_executions=500

# Single log file for all executions
log_file="loop_replay.log"

# Start time of the entire script
script_start_time=$(date +%s)

for ((i = 0; i < num_executions; i++)); do
    echo "Replay iteration: $((i+1))" | tee -a "$log_file"
    
    # Measure the time taken for each command execution
    iteration_start_time=$(date +%s)

    # Execute the command and display output only on the console
    { time $command; } 2>&1 | grep -E '^(real|user|sys)' | tee -a "$log_file"
	
    iteration_end_time=$(date +%s)
    iteration_duration=$((iteration_end_time - iteration_start_time))
    
    echo "Iteration $((i+1)) took $iteration_duration seconds" | tee -a "$log_file"

    # sleep (duration in secs) before next execution
    sleep 2

done

# End time of the entire script
script_end_time=$(date +%s)
script_duration=$((script_end_time - script_start_time))

echo "The entire script took $script_duration seconds" | tee -a "$log_file"
