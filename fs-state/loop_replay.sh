#!/bin/bash

# Replayer command to execute
command="sudo ./replay -K 0:ext4:256:jfs:16384"

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
