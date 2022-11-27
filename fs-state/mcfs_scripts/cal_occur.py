import csv
import re

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
