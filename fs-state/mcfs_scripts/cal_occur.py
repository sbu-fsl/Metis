import csv

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
         'setxattr',
         'removexattr',
         'mknod',
         'fallocate']

header = ['Operation', 'Occur_Times_' + time_lengths[0], 'Occur_Times_' + time_lengths[1]]

file0 = open(file_names[0], 'r')
file1 = open(file_names[1], 'r')

occur_f = open('occur_stats.csv', 'w')
occur_csvwriter = csv.writer(occur_f) 
occur_csvwriter.writerow(header)

fcont0 = file0.read()
fcont1 = file1.read()

for each_op in fsops:
    occurs0 = fcont0.count(each_op)
    occurs1 = fcont1.count(each_op)
    occur_csvwriter.writerow([each_op, occurs0, occurs1])

occur_f.close()
file1.close()
file0.close()
