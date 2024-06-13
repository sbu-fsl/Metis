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

import csv
import re

file_names = ['/mcfs/gcov_test_2022_1029/yf-filesystem-utility/gcov-coverage-for-other-fs-checkers-2022-1109/nfs4mc/fs-state/sequence-pan-20221114-140531-1201260.log',
            '/mcfs/gcov_test_2022_1029/yf-filesystem-utility/gcov-coverage-for-other-fs-checkers-2022-1109/nfs4mc/fs-state/sequence-pan-20221114-145748-1302543.log']

time_lengths = ['30mins', '60mins']

fsops = ['create_file',
         'write_file',
         'truncate',
         'unlink',
         'mkdir',
         'rmdir',
         'chmod',
         'chown_file',
         'chgrp_file',
         'setxattr',
         'removexattr',
         'fallocate_file',
         'rename',
         'link',
         'symlink']

seq_dir = '/Users/yifeiliu/Downloads/Swarm6VTs20hoursExt4only8MiBResults/Ext4-only-gcov-20hours-6VTs-20221124-212805-306063/'
seq_files = ['sequence-pan1-20221124-212805-306063.log',
            'sequence-pan2-20221124-212805-306064.log',
            'sequence-pan3-20221124-212805-306065.log',
            'sequence-pan4-20221124-212805-306066.log',
            'sequence-pan5-20221124-212805-306067.log',
            'sequence-pan6-20221124-212805-306068.log']

header = ['Operations_in_the_Driver'] + ['pan1', 'pan2', 'pan3', 'pan4', 'pan5', 'pan6']

occur_f = open('occur_stats.csv', 'w')
occur_csvwriter = csv.writer(occur_f) 
occur_csvwriter.writerow(header)

for i in range(len(fsops)):
    row = [fsops[i]]
    for j in range(len(seq_files)):
        file = open(seq_dir + seq_files[j], 'r')
        fcont = file.read()
        occurs = len(re.findall(r'\b'+ fsops[i] + r'\b', fcont, re.IGNORECASE))
        row.append(occurs)
        file.close()
    occur_csvwriter.writerow(row)

occur_f.close()
