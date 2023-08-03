#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

// Probability of choosing each open flag bit (e.g., 0.5: 50% each bit is set to 1)
#define UNIFORM_FLAG_RATE 0.5
// If it's 1 use uniform open flags for driver, otherwise use pre-defined probabilistic open flags
#define IS_UNIFORM_FLAG 1
// Maximum open flags: otcal 037777777 (11111111111111111111111) = 23 bits
#define MAX_FLAG_BITS 23
// Scale the probabilities in flagBitPercent by multiplying this PROB_FACTOR
// PROB_FACTOR == 1 means do not scale the probabilities
// PROB_FACTOR > 1 means increase the probabilities
// 0 < PROB_FACTOR < 1 means decrease the probabilities
#define PROB_FACTOR 1

// Probable weight for each open flags
// Does not need to be real percentage value, can represent weights for each flag
const double flagBitPercent = {
    10.12, //	O_WRONLY	0
    9.02, //	O_RDWR	1
    0.00, //	N/A	2
    0.00, //	N/A	3
    0.00, //	N/A	4
    0.00, //	N/A	5
    13.87, //	O_CREAT	6
    7.49, //	O_EXCL	7
    0.69, //	O_NOCTTY	8
    9.43, //	O_TRUNC	9
    4.58, //	O_APPEND	10
    9.15, //	O_NONBLOCK	11
    2.77, //	O_DSYNC	12
    2.36, //	FASYNC	13
    10.68, //	O_DIRECT	14
    5.41, //	O_LARGEFILE	15
    2.50, //	O_DIRECTORY	16
    1.39, //	O_NOFOLLOW	17
    2.22, //	O_NOATIME	18
    4.16, //	O_CLOEXEC	19
    0.97, //	__O_SYNC	20
    2.77, //	O_PATH	21
    0.42 //	__O_TMPFILE	22
};

int create_file(const char *path, int flags, int mode);
ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length);
int fallocate_file(const char *path, off_t offset, off_t len);
int chown_file(const char *path, uid_t owner);
int chgrp_file(const char *path, gid_t group);

#endif // _OPERATIONS_H
