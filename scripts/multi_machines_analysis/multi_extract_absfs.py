#!/usr/bin/env python3

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

import re
import glob

from sys import argv
import os
import socket
import gzip

absfs_pat = re.compile(r'\[\s*(\d+\.\d+)\] absfs = \{([0-9a-z]+)\}')

def is_gz_file(filename):
    root, ext = os.path.splitext(filename)
    return ext == '.gz'

if __name__ == '__main__':
    # File name pattern for `ls` command
    if len(argv) < 3:
        print('Usage: %s <number-of-VTs> <filename-pattern>' % argv[0])
        exit(1)

    vt_num = int(argv[1])
    fnpattern = argv[2]
    flist = glob.glob(fnpattern, recursive=True) 
    host_name = socket.gethostname()

    for fpath in flist:
        # host_name: sgdp02, sgdp03, yifeilatest3, etc.
        # vt_number: 4, 8, 12, 16, etc. that represents the number of VTs
        # pan_name: pan1, pan2, pan3, etc.
        if not os.path.exists(fpath):
            raise FileNotFoundError(f"No file found at {fpath}")
        pan_name = fpath.split('/')[-1].split('-')[1]
        each_abs_path = 'time-absfs-%s-VT%d-%s.csv' % (host_name, vt_num, pan_name)
        out_fp = open(each_abs_path, 'a')
        fp = None
        # Check if the file is a gzip file
        if is_gz_file(fpath):
            fp = gzip.open(fpath, 'rt', encoding='utf-8') 
        else:
            fp = open(fpath, 'r')
        if fp is None:
            raise Exception(f"Failed to open file {fpath}")
        try:
            for line in fp:
                result = absfs_pat.match(line)
                if result is None:
                    continue
                timestamp = result.group(1)
                absfs = result.group(2)
                out_fp.write('%s,%s\n' % (timestamp, absfs))
        finally:
            fp.close()
            out_fp.close()

    print('All extract-time-absfs for Swarm VTs completed!')
