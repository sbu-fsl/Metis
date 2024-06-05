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
num_executions=1

for ((i = 0; i < num_executions; i++)); do
	echo "Replay iteration: $((i+1))"
	echo

	log_file="loop_replay_$((i + 1)).log"

    # Execute the command and capture output
    $command > "$log_file" 2>&1

    # Print output to console as well
    cat "$log_file"

    # sleep (duration in secs) before next execution
    sleep 5
done