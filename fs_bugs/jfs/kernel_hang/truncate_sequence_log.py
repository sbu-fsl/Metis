sequence_log_file_path = 'sequence-pan-20240209-182859-244192_kh6.log'
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