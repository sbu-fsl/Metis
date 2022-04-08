#!/usr/bin/env python3

import re
import subprocess as sp

from sys import argv
import os

absfs_pat = re.compile(r'\[\s*(\d+\.\d+)\] absfs = \{([0-9a-z]+)\}')


def get_filelist(pattern='.'):
    p = sp.Popen('ls -tr %s' % pattern, shell=True, stdout=sp.PIPE)
    ret = p.wait()
    if ret != 0:
        raise Exception('Listing failed, return value is %d' % ret)
    return p.stdout.read().decode('utf-8').splitlines()


if __name__ == '__main__':
    # File name pattern for `ls` command
    if len(argv) < 2:
        print('Usage: %s <filename-pattern>' % argv[0])
        exit(1)

    fnpattern = argv[1]
    flist = get_filelist(fnpattern)

    for fpath in flist:
        # pan_name: pan1, pan2, pan3, etc.
        pan_name = fpath.split('/')[-1].split('-')[1]
        each_abs_path = 'time-absfs-%s.csv' % pan_name
        if os.path.exists(each_abs_path):
            os.remove(each_abs_path)
        out_fp = open(each_abs_path, 'a')
        fp = open(fpath, 'r')
        try:
            for line in fp:
                result = absfs_pat.match(line)
                if result is None:
                    continue
                timestamp = result.group(1)
                absfs = result.group(2)
                #print('%s,%s' % (timestamp, absfs))
                out_fp.write('%s,%s\n' % (timestamp, absfs))
        finally:
            fp.close()
            out_fp.close()
