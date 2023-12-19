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

flag_probs = [
    10.12, #	O_WRONLY	0
    9.02, #	O_RDWR	1
    0.00, #	N/A	2
    0.00, #	N/A	3
    0.00, #	N/A	4
    0.00, #	N/A	5
    13.87, #	O_CREAT	6
    7.49, #	O_EXCL	7
    0.69, #	O_NOCTTY	8
    9.43, #	O_TRUNC	9
    4.58, #	O_APPEND	10
    9.15, #	O_NONBLOCK	11
    2.77, #	O_DSYNC	12
    2.36, #	FASYNC	13
    10.68, #	O_DIRECT	14
    5.41, #	O_LARGEFILE	15
    2.50, #	O_DIRECTORY	16
    1.39, #	O_NOFOLLOW	17
    2.22, #	O_NOATIME	18
    4.16, #	O_CLOEXEC	19
    0.97, #	__O_SYNC	20
    2.77, #	O_PATH	21
    0.42 #	__O_TMPFILE	22
]

# Substraction from 100% to get the inverse probability
# inverse_probs = [100 - x for x in flag_probs]

# Use reciprocal
percent_flags = [x / 100 for x in flag_probs]
inverse_probs = [1 / x if x != 0 else 0 for x in percent_flags]

print('inverse_probs: ', inverse_probs)

# Normalize to be percent [0, 1]
total = sum(inverse_probs)
normalized_invs = [(x / total) * 100 for x in inverse_probs]

print('normalized_invs: ', normalized_invs)
