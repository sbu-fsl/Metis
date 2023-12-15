#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#


# Check if output-pan*.*.log.gz files are decompressed to output-pan*.*.log

# output-pan[number]-[number]-[number]-[number].[number].log.gz
# output-pan*-*-*-*.*.log.gz

# Loop through all .log.gz files matching the specified pattern
for gzfile in output-pan*-*-*-*.*.log.gz; do
    # Check if the file exists (in case the pattern doesn't match any files)
    if [[ -f "$gzfile" ]]; then
        # Remove the .gz extension to get the name of the decompressed file
        log_file="${gzfile%.gz}"

        # Check if the decompressed file exists
        if [[ -f "$log_file" ]]; then
            # Print the name of the decompressed file
            echo "$log_file"
            # Delete all these decompressed log files
            # rm "$log_file"
            # echo "Deleting $log_file..."
        fi
    fi
done

echo "All completed."
