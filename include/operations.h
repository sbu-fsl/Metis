#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stddef.h>
#include <sys/types.h>
#include <stdint.h>
#include <math.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

// Maximum open flags: otcal 037777777 (11111111111111111111111) = 23 bits
#define MAX_FLAG_BITS 23

/* 
 * CONFIGURABLE MACROS
 */

// Ration in rank-size distribution or sampling
#define RZD_RATIO 0.9

// 0 - uniform, 1 - probability, 2 - Inverse by harmonic mean weighting, 3 - Inverse by subtraction from 100%
// 4 - rank-size distribution (based on RZD_RATIO), 5 - Inverse rank-size distribution (based on RZD_RATIO) 
#define OPEN_FLAG_PATTERN 0

// Probability of choosing each open flag bit (e.g., 0.5: 50% each bit is set to 1)
// CONFIGURE PROB_FACTOR if OPEN_FLAG_PATTERN == 0
#define UNIFORM_FLAG_RATE 0.5
/* Scale the probabilities in flagBitPercent by multiplying this PROB_FACTOR
 * PROB_FACTOR == 1 means do not scale the probabilities
 * PROB_FACTOR > 1 means increase the probabilities
 * 0 < PROB_FACTOR < 1 means decrease the probabilities
 */
// CONFIGURE PROB_FACTOR if OPEN_FLAG_PATTERN == 1 or 2 or 3
// #define PROB_FACTOR 1
#define PROB_FACTOR 5

// Write size configurable macros
// 0 - uniform distribution, 1 - RZD normalization, 2 - Inverse RZD normalization
#define WRITE_SIZE_PATTERN 1

// Marcos to distinguish open flags for different operations
#define USE_CREATE_FLAG 0
#define USE_WRITE_FLAG 1

// Write size fixed macros
#define WRITE_SIZE_PARTS 33

// Rank-size distribution for write size 
#define WRITE_SIZE_RZD_RATIO 0.9

typedef struct all_inputs {
    int create_open_flag;
    int write_open_flag;
    size_t write_size;
} inputs_t;

extern inputs_t *inputs_t_p;

/* Write size partition data structure */
typedef struct write_size_partition {
    size_t minsz;
    size_t maxsz;
} writesz_partition_t;

// We investigate 34 write size partitions: equal to 0, 0, 1, ... 31, 32
writesz_partition_t writesz_parts[WRITE_SIZE_PARTS];

// Random integer generator [min, max] included
static inline size_t rand_size(size_t min, size_t max)
{
   return min + rand() % (max + 1 - min);
}

void populate_writesz_parts();

void syscall_inputs_init();

// Probable weight for each open flags
// Does not need to be real percentage value, as long as it can represent weights for each flag
/*
 * TODO: more flexible Probabilities Three different variants: uniform, prob, inverse-prob
 * 1. Probabilities in the kernel
 * 2. Inverse variant probs: more occurrence in the kernel, less prob to be chosen (think about it)
 * Find out the inverse probality of each flag bit
 */
extern const double flagBitPercent[MAX_FLAG_BITS];

extern double whmFlagPercent[MAX_FLAG_BITS];
extern double subFlagPercent[MAX_FLAG_BITS];
extern double rzdFlagPercent[MAX_FLAG_BITS];
extern double inv_rzdFlagPercent[MAX_FLAG_BITS];

int create_file(const char *path, int flags, int mode);
ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length);
int fallocate_file(const char *path, off_t offset, off_t len);
int chown_file(const char *path, uid_t owner);
int chgrp_file(const char *path, gid_t group);

// Driver functions
int pick_open_flags(int pattern, int ops);
size_t pick_write_sizes(int pattern);

#endif // _OPERATIONS_H
