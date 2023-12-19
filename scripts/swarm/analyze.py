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

import sys

absfs = {
    'pan1': [],
    'pan2': [],
    'pan3': [],
    'pan4': []
}


def loadall():
    for inst in absfs.keys():
        fp = open('time-absfs-%s.log' % inst, 'r')
        print('Loading time-absfs file for %s...' % inst, file=sys.stderr)
        try:
            for line in fp:
                timestamp, state = line.split(',')
                timestamp = float(timestamp)
                absfs[inst].append((timestamp, state))
        finally:
            fp.close()
        pass

sets = {
    'pan1': set(), 'pan2': set(),
    'pan3': set(), 'pan4': set()
}
last_offset = {
    'pan1': 0, 'pan2': 0, 'pan3': 0, 'pan4': 0
}


def analyze(end_secs):
    res = {}
    # load set
    for inst in absfs.keys():
        fp = open('time-absfs-%s.log' % inst, 'r')
        fp.seek(last_offset[inst])
        line = fp.readline()
        while line:
            ts, value = line.split(',')
            ts = float(ts)
            sets[inst].add(value)
            if ts > end_secs:
                break
            line = fp.readline()
        last_offset[inst] = fp.tell()
        fp.close()
    # Compute numbers
    res['pan1 & pan2'] = len(sets['pan1'] & sets['pan2'])
    res['pan1 U pan2'] = len(sets['pan1'] | sets['pan2'])
    res['pan1 & pan3'] = len(sets['pan1'] & sets['pan3'])
    res['pan1 U pan3'] = len(sets['pan1'] | sets['pan3'])
    res['pan1 & pan4'] = len(sets['pan1'] & sets['pan4'])
    res['pan1 U pan4'] = len(sets['pan1'] | sets['pan4'])
    res['pan2 & pan3'] = len(sets['pan2'] & sets['pan3'])
    res['pan2 U pan3'] = len(sets['pan2'] | sets['pan3'])
    res['pan2 & pan4'] = len(sets['pan2'] & sets['pan4'])
    res['pan2 U pan4'] = len(sets['pan2'] | sets['pan4'])
    res['pan3 & pan4'] = len(sets['pan3'] & sets['pan4'])
    res['pan3 U pan4'] = len(sets['pan3'] | sets['pan4'])
    res['all_intersect'] = len(sets['pan1'] & sets['pan2'] & sets['pan3'] & sets['pan4'])
    res['all_union'] = len(sets['pan1'] | sets['pan2'] | sets['pan3'] | sets['pan4'])
    res['by_twomore'] = len(
        (sets['pan1'] & sets['pan2']) |
        (sets['pan1'] & sets['pan3']) |
        (sets['pan1'] & sets['pan4']) |
        (sets['pan2'] & sets['pan3']) |
        (sets['pan2'] & sets['pan4']) |
        (sets['pan3'] & sets['pan4'])
    )
    return res


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: %s <max-hours>' % sys.argv[0])
        exit(1)

    max_hours = int(sys.argv[1])
    # load time-absfs files
    # loadall()
    # print header
    print('time_secs,pan1 & pan2,pan1 U pan2,overlap_pan1_pan2,', end='')
    print('pan1 & pan3,pan1 U pan3,overlap_pan1_pan3,', end='')
    print('pan1 & pan4,pan1 U pan4,overlap_pan1_pan4,', end='')
    print('pan2 & pan3,pan2 U pan3,overlap_pan2_pan3,', end='')
    print('pan2 & pan4,pan2 U pan4,overlap_pan2_pan4,', end='')
    print('pan3 & pan4,pan3 U pan4,overlap_pan3_pan4,', end='')
    print('total_unique_states,partial_overlap,partial_waste_ratio,', end='')
    print('total_overlap,total_waste_ratio')
    # compute each hour
    for hr in range(max_hours):
        ts = (hr + 1) * 3600
        res = analyze(ts)
        # print fields
        print('%d,%d,%d,%.6f' % (ts, res['pan1 & pan2'], res['pan1 U pan2'], res['pan1 & pan2'] / res['pan1 U pan2']), end=',')
        print('%d,%d,%.6f' % (res['pan1 & pan3'], res['pan1 U pan3'], res['pan1 & pan3'] / res['pan1 U pan3']), end=',')
        print('%d,%d,%.6f' % (res['pan1 & pan4'], res['pan1 U pan4'], res['pan1 & pan4'] / res['pan1 U pan4']), end=',')
        print('%d,%d,%.6f' % (res['pan2 & pan3'], res['pan2 U pan3'], res['pan2 & pan3'] / res['pan2 U pan3']), end=',')
        print('%d,%d,%.6f' % (res['pan2 & pan4'], res['pan2 U pan4'], res['pan2 & pan4'] / res['pan2 U pan4']), end=',')
        print('%d,%d,%.6f' % (res['pan3 & pan4'], res['pan3 U pan4'], res['pan3 & pan4'] / res['pan3 U pan4']), end=',')
        print('%d,%d,%.6f' % (res['all_union'], res['by_twomore'], res['by_twomore'] / res['all_union']), end=',')
        print('%d,%.6f' % (res['all_intersect'], res['all_intersect'] / res['all_union']))

