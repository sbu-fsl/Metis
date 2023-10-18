#define _GNU_SOURCE
#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

inputs_t *inputs_t_p = NULL;

writesz_partition_t writesz_parts[WRITE_SIZE_PARTS];

double whmFlagPercent[MAX_FLAG_BITS] = {0};
double subFlagPercent[MAX_FLAG_BITS] = {0};
double rzdFlagPercent[MAX_FLAG_BITS] = {0};
double inv_rzdFlagPercent[MAX_FLAG_BITS] = {0};
double rzdWriteSizePrecent[WRITE_SIZE_PARTS] = {0};
double inv_rzdWriteSizePrecent[WRITE_SIZE_PARTS] = {0};

// Based on the kernel ocurrence probability 
const double flagBitPercent[MAX_FLAG_BITS] = {
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

// Rank: 0 invalid bits
// Rank: 1 most occurred bits Rank: 19 least occurred bits
const double flagKernOcurRank[MAX_FLAG_BITS] = {
    3, 6, 0, 0, 0, 0, 1, 7, 18, 4, 9, 5, 11, 14, 2, 8, 13, 16, 15, 10, 17, 11, 19
};

// Rank: 0 invalid bits
// Rank: 1 least occurred bits Rank: 19 most occurred bits
const double inv_flagKernOcurRank[MAX_FLAG_BITS] = {
    17, 14, 0, 0, 0, 0, 19, 13, 2, 16, 11, 15, 8, 6, 18, 12, 7, 4, 5, 10, 3, 8, 1
};


int create_file(const char *path, int flags, int mode)
{
    int fd = open(path, flags, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length)
{
    int fd = open(path, flags, O_RDWR);
    int err;
    if (fd < 0) {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit_err;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int fallocate_file(const char *path, off_t offset, off_t len)
{
    int fd = open(path, O_RDWR);
    int err;
    int ret = -1;
    if (fd < 0) {
        err = errno;
        return -1;
    }
    ret = fallocate(fd, 0, offset, len);
    if (ret < 0) {
        err = errno;
        goto exit_err;
    }
    close(fd);
    return ret;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int chown_file(const char *path, uid_t owner)
{
    return chown(path, owner, -1);
}

int chgrp_file(const char *path, gid_t group)
{
    return chown(path, -1, group);
}

/* MCFS DRIVER FUNCTIONS FOR INPUT COVERAGE */

void populate_writesz_parts()
{
    writesz_parts[0].minsz = 0;
    writesz_parts[0].maxsz = 0;

    uint64_t minval = 0;
    uint64_t maxval = 0;

    for (int i = 1; i < WRITE_SIZE_PARTS; ++i) {
        minval = pow(2, i - 1);
        maxval = pow(2, i) - 1;

        writesz_parts[i].minsz = minval;
        writesz_parts[i].maxsz = maxval;
    }
    
    /*
    // Dump rank-size distribution open flags
    for (int i = 0; i < MAX_FLAG_BITS; ++i) {
        fprintf(stdout, "rzdFlagPercent[%d] = %f\n", i, rzdFlagPercent[i]);
    }
    fprintf(stdout, "=====================\n");
    for (int i = 0; i < MAX_FLAG_BITS; ++i) {
        fprintf(stdout, "inv_rzdFlagPercent[%d] = %f\n", i, inv_rzdFlagPercent[i]);
    }
    fflush(stdout);
    */

    /*
    // Dump RZDN and Inverse RZDN write size probablities array
    for (int i = 0; i < WRITE_SIZE_PARTS; ++i) {
        fprintf(stdout, "rzdWriteSizePrecent[%d] = %f\n", i, rzdWriteSizePrecent[i]);
    }
    fprintf(stdout, "=====================\n");
    for (int i = 0; i < WRITE_SIZE_PARTS; ++i) {
        fprintf(stdout, "inv_rzdWriteSizePrecent[%d] = %f\n", i, inv_rzdWriteSizePrecent[i]);
    }
    fflush(stdout);
    */

    /*
    // Dump inverse write probability arrays
    for (int i = 0; i < MAX_FLAG_BITS; ++i) {
        fprintf(stdout, "whmFlagPercent[%d] = %f\n", i, whmFlagPercent[i]);
    }
    fprintf(stdout, "=====================\n");
    for (int i = 0; i < MAX_FLAG_BITS; ++i) {
        fprintf(stdout, "subFlagPercent[%d] = %f\n", i, subFlagPercent[i]);
    }
    fflush(stdout);
    */

    /*
    // Dump write size partitions
    fprintf(stdout, "DRIVER write size partitions:\n");
    fprintf(stdout, "The maximum value of size_t is: %zu\n", SIZE_MAX);
    for (int i = 0; i < WRITE_SIZE_PARTS; ++i) {
        fprintf(stdout, "writesz_parts[%d]: minsz = %zu, maxsz = %zu\n", 
            i, writesz_parts[i].minsz, writesz_parts[i].maxsz);
    }
    // flush stdout, otherwise write size cannot be dumped
    fflush(stdout);
    */
}

void syscall_inputs_init()
{
    srand(time(0));
    inputs_t_p = (inputs_t *)malloc(sizeof(inputs_t));
    if (inputs_t_p == NULL) {
        fprintf(stderr, "Error: malloc failed for syscall_inputs_init\n");
        exit(1);
    }
    inputs_t_p->create_open_flag = 0;
    inputs_t_p->write_open_flag = 0;
    /* 
     * Inverse option 1: populate whmFlagPercent array based on flagBitPercent
     * Reciprocal then normalize to 100%
     */
    double total = 0.0;
    // Reciprocal
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        if (flagBitPercent[i] == 0) {
            whmFlagPercent[i] = 0;
        }
        else {
            whmFlagPercent[i] = 1 / flagBitPercent[i];
        }
        total += whmFlagPercent[i];
    }
    // Normalize to 100%
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        whmFlagPercent[i] = (whmFlagPercent[i] / total) * 100;
    }
    /* 
     * Inverse option 2: populate subFlagPercent array based on flagBitPercent
     * Subtract from 100% then normalize to 100%
     */

    total = 0.0;
    // Subtract from 100% and calculate total
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        subFlagPercent[i] = 100 - flagBitPercent[i];
        total += subFlagPercent[i];
    }
    // Normalize to 100%
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        subFlagPercent[i] = subFlagPercent[i] / total * 100;
    }
    /*
     * Rank-size distribution or sampling
     */
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        if (flagKernOcurRank[i] == 0) {
            rzdFlagPercent[i] = 0;
        }
        else {
            rzdFlagPercent[i] = pow(RZD_RATIO, flagKernOcurRank[i]);
        }
    }
    /*
     * Inverse rank-size distribution or sampling
     */
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        if (inv_flagKernOcurRank[i] == 0) {
            inv_rzdFlagPercent[i] = 0;
        }
        else {
            inv_rzdFlagPercent[i] = pow(RZD_RATIO, inv_flagKernOcurRank[i]);
        }
    }
    // Init write RZD normalization write size probablity array
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        rzdWriteSizePrecent[i] = pow(WRITE_SIZE_RZD_RATIO, i+1);
    }
    // Normalize rzdWriteSizePrecent to sum as 100%
    total = 0.0;
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        total += rzdWriteSizePrecent[i];
    }
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        rzdWriteSizePrecent[i] = rzdWriteSizePrecent[i] / total;
    }
    // Init write inverse RZD normalization write size probablity array
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        inv_rzdWriteSizePrecent[i] = pow(WRITE_SIZE_RZD_RATIO, WRITE_SIZE_PARTS - i);
    }
    // Normalize inv_rzdWriteSizePrecent to sum as 100%
    total = 0.0;
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        total += inv_rzdWriteSizePrecent[i];
    }
    for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
        inv_rzdWriteSizePrecent[i] = inv_rzdWriteSizePrecent[i] / total;
    }
    // Init write size partition array
    populate_writesz_parts();
}

/*
 * Pattern: 0 - uniform, 1 - probability, 2 - inversed probability
 * Ops: 0 - create, 1 - write
 */
int pick_open_flags(int pattern, int ops)
{
    // srand(time(0)) already called at syscall_inputs_init()
    int flags = 0;
    // Uniform 
    if (pattern == 0) {
        for (int i = 0; i < MAX_FLAG_BITS; i++) {
            // [0, 1) (i.e., up to but not including 1)
            if ((double)rand() / (RAND_MAX) < UNIFORM_FLAG_RATE) {
                flags |= 1 << i;
            }
        }
    }
    // Probability
    else if (pattern == 1) {
        for (int i = 0; i < sizeof(flagBitPercent)/sizeof(flagBitPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) * 100 < flagBitPercent[i] * PROB_FACTOR) {
                flags |= 1 << i;
            }
        }
    }
    // Inversed probability by weighted harmonic mean (reciprocal then normalize to 100%)
    else if (pattern == 2) {
        for (int i = 0; i < sizeof(whmFlagPercent)/sizeof(whmFlagPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) * 100 < whmFlagPercent[i] * PROB_FACTOR) {
                flags |= 1 << i;
            }
        }
    }
    // Inversed probability by substraction from 100% then normalize to 100%
    else if (pattern == 3) {
        for (int i = 0; i < sizeof(subFlagPercent)/sizeof(subFlagPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) * 100 < subFlagPercent[i] * PROB_FACTOR) {
                flags |= 1 << i;
            }
        }        
    }
    // RZD: Rank-size distribution or sampling
    else if (pattern == 4) {
        for (int i = 0; i < sizeof(rzdFlagPercent)/sizeof(rzdFlagPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) < rzdFlagPercent[i]) {
                flags |= 1 << i;
            }
        }
    }
    // Inverse Rank-size distribution or sampling
    else if (pattern == 5) {
        for (int i = 0; i < sizeof(inv_rzdFlagPercent)/sizeof(inv_rzdFlagPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) < inv_rzdFlagPercent[i]) {
                flags |= 1 << i;
            }
        }
    }
    // Not recognized
    else {
        fprintf(stderr, "Error: invalid open flags pattern\n");
        exit(1);
    }
    if (ops == USE_CREATE_FLAG) {
        inputs_t_p->create_open_flag = flags;
    }
    else if (ops == USE_WRITE_FLAG) {
        inputs_t_p->write_open_flag = flags;
    }
    else {
        fprintf(stderr, "Error: invalid open flags ops\n");
        exit(1);
    }
    return flags;
}

size_t pick_write_sizes(int pattern)
{
    size_t writesz = 0;
    // Uniform
    if (pattern == 0) {
        // Pick a partition with an uniform probability
        int uni_idx = (int)(rand() / ((double)RAND_MAX + 1) * WRITE_SIZE_PARTS);
        // Randomly pick a write size in a partition [minsz, maxsz]
        writesz = rand_size(writesz_parts[uni_idx].minsz, writesz_parts[uni_idx].maxsz);
    }
    // Rank Size Distribution, then Normalize (RZDN)
    else if (pattern == 1) {
        double sum = 0;
        // Pick a write size partition based on rzdWriteSizePrecent
        double randNum = (float)rand() / RAND_MAX;
        for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
            sum += rzdWriteSizePrecent[i];
            if (randNum <= sum) {
                // Randomly pick a write size in a partition [minsz, maxsz]
                writesz = rand_size(writesz_parts[i].minsz, writesz_parts[i].maxsz);
                break;
            }
        }

    }
    // Inverse Rank Size Distribution, then Normalize (IRZDN)
    else if (pattern == 2) {
        double sum = 0;
        // Pick a write size partition based on inv_rzdWriteSizePrecent
        double randNum = (float)rand() / RAND_MAX;
        for (int i = 0; i < WRITE_SIZE_PARTS; i++) {
            sum += inv_rzdWriteSizePrecent[i];
            if (randNum <= sum) {
                // Randomly pick a write size in a partition [minsz, maxsz]
                writesz = rand_size(writesz_parts[i].minsz, writesz_parts[i].maxsz);
                break;
            }
        }
    }
    inputs_t_p->write_size = writesz;
    return writesz;
}
