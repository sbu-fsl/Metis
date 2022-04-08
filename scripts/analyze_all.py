#!/usr/bin/env python3

import sys
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('-m', '--maxHours', type=int, help='max hours to consider')
parser.add_argument('-n', '--numPan', type=int, help='number of pan')
args = parser.parse_args()
max_hours = int(args.maxHours)
num_pan = int(args.numPan)
#print('max hours: %s' % max_hours)
#print('number of pan: %s' % num_pan)

# print header
print('time_secs,', end='')
print('total_unique_states,partial_overlap,partial_waste_ratio,', end='')
print('total_overlap,total_waste_ratio,', end='')
for i in range(1, num_pan + 1):
    for j in range(i + 1, num_pan + 1):
        print('pan%d & pan%d,pan%d U pan%d,overlap_pan%d_pan%d,' % (i, j, i, j, i, j), end='')
print('')

# init absfs
absfs = {}
for i in range(1, num_pan + 1):
    absfs['pan%d' % i] = []

# init sets
sets = {}
for i in range(1, num_pan + 1):
    sets['pan%d' % i] = set()

# init last_offset
last_offset = {}
for i in range(1, num_pan + 1):
    last_offset['pan%d' % i] = 0

def analyze(end_secs):
    res = {}
    # load set
    for inst in absfs.keys():
        fp = open('time-absfs-%s.csv' % inst, 'r')
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
    # Compute pair intersection and union numbers
    for i in range(1, num_pan + 1):
        for j in range(i + 1, num_pan + 1):
            res['pan%d & pan%d' % (i, j)] = len(sets['pan%d' % i] & sets['pan%d' % j])
            res['pan%d U pan%d' % (i, j)] = len(sets['pan%d' % i] | sets['pan%d' % j])
    # Compute all intersect number
    all_intersect_set = sets['pan1']
    for i in range(2, num_pan + 1):
        all_intersect_set = all_intersect_set & sets['pan%d' % i]
    res['all_intersect'] = len(all_intersect_set)
    # Compute all union number
    all_union_set = sets['pan1']
    for i in range(2, num_pan + 1):
        all_union_set = all_union_set | sets['pan%d' % i]
    res['all_union'] = len(all_union_set)
    # Compute states visited by at least two verification tasks (pan)
    by_twomore_set = sets['pan1'] & sets['pan2']
    for i in range(1, num_pan + 1):
        for j in range(i + 1, num_pan + 1):
            if i == 1 and j == 2:
                continue
            by_twomore_set = by_twomore_set | (sets['pan%d' % i] & sets['pan%d' % j])
    res['by_twomore'] = len(by_twomore_set)
    return res

# compute each hour
for hr in range(max_hours):
    ts = (hr + 1) * 3600
    res = analyze(ts)
    # print fields
    print('%d' % ts, end=',')
    print('%d,%d,%.6f' % (res['all_union'], res['by_twomore'], res['by_twomore'] / res['all_union']), end=',')
    print('%d,%.6f' % (res['all_intersect'], res['all_intersect'] / res['all_union']), end=',')
    for i in range(1, num_pan + 1):
        for j in range(i + 1, num_pan + 1):
            if i == num_pan - 1 and j == num_pan:
                print('%d,%d,%.6f' % (res['pan%d & pan%d' % (i, j)], res['pan%d U pan%d' % (i, j)], res['pan%d & pan%d' % (i, j)] / res['pan%d U pan%d' % (i, j)]))
            else:
                print('%d,%d,%.6f' % (res['pan%d & pan%d' % (i, j)], res['pan%d U pan%d' % (i, j)], res['pan%d & pan%d' % (i, j)] / res['pan%d U pan%d' % (i, j)]), end=',')
