#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stddef.h>
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

// 0 - uniform, 1 - probability, 2 - inversed probability
#define OPEN_FLAG_PATTERN 0 

/* 
 * Currently we don't add "size_t write_size;" to the struct
 * because we can use if...fi to select write size
 */
typedef struct all_inputs {
    int open_flag;
} inputs_t;

extern inputs_t *inputs_t_p;

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

extern double inverseFlagPercent[MAX_FLAG_BITS];

int create_file(const char *path, int flags, int mode);
ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length);
int fallocate_file(const char *path, off_t offset, off_t len);
int chown_file(const char *path, uid_t owner);
int chgrp_file(const char *path, gid_t group);

#endif // _OPERATIONS_H
