#!/usr/bin/env python3

# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2023-2024 Divyaank Tiwari
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache
# License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).

# This python code simply takes a log file having operations for both ext4 and JFS file systems
# and truncates the log to only have operations from JFS
sequence_log_file_path = 'jfs_kernel_hang_sequence.log'
truncated_sequence_log_file_path = 'jfs_op_sequence.log'

# Open the input file and output file
with open(sequence_log_file_path, 'r') as infile, open(truncated_sequence_log_file_path, 'w') as outfile:
    # Iterate over each line in the input file
    for line in infile:
        # Check if the substring 'jfs' is in the current line
        if 'jfs' in line:
            # Write the line to the output file
            if 'setxattr' in line or 'removexattr' in line:
                continue
            else:
                outfile.write(line)
