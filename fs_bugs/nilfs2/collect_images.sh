#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Jerry Kang
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

# May need to change FILEDIR_EXIST_PROB to 0 before running this script

MCFSDIR="/mcfs/jfs-mcfs-2023-0427/nfs4mc"

# Define the number of iterations
iterations=10

# Define the destination folder
destination_folder="$MCFSDIR/reproduce_oops"

# Create the destination folder if it doesn't exist
mkdir -p "$destination_folder"

# Loop from 1 to the defined number of iterations
for ((i=1; i<=iterations; i++))
do
    # Run MCFS
    cd $MCFSDIR/fs-state/mcfs_scripts
    ./single_nilfs2.sh

    sleep 2

    # Copy the file to the destination folder
    cd $MCFSDIR/fs-state
    cp cbuf-nilfs2*0.img "$destination_folder/$(printf "%03d" "$i").img"

    # clean the directory
    make clean

    # Print a message for the current iteration
    echo "Iteration $i completed."
done

