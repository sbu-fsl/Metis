#!/bin/bash

# Define the number of iterations
iterations=10

# Define the destination folder
destination_folder="/home/ubuntu/testing/reproduce_oops"

# Create the destination folder if it doesn't exist
mkdir -p "$destination_folder"

# Loop from 1 to the defined number of iterations
for ((i=1; i<=iterations; i++))
do
    # Run MCFS
    cd /home/ubuntu/nfs4mc/fs-state/mcfs_scripts
    ./nilfs2_single.sh

    sleep 2

    # Copy the file to the destination folder
    cd /home/ubuntu/nfs4mc/fs-state
    cp cbuf-nilfs2*0.img "$destination_folder/$(printf "%03d" "$i").img"

    # clean the directory
    make clean

    # Print a message for the current iteration
    echo "Iteration $i completed."
done

