#define _GNU_SOURCE
#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

inputs_t *inputs_t_p = NULL;

double inverseFlagPercent[MAX_FLAG_BITS] = {0};

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
    // Populate inverseFlagPercent array based on flagBitPercent
    double total = 0;
    // Subtract from 100% and calculate total
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        inverseFlagPercent[i] = 100 - flagBitPercent[i];
        total += inverseFlagPercent[i];
    }
    // Normalize to 100%
    for (int i = 0; i < MAX_FLAG_BITS; i++) {
        inverseFlagPercent[i] = inverseFlagPercent[i] / total * 100;
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
    // Inversed probability
    else if (pattern == 2) {
        for (int i = 0; i < sizeof(inverseFlagPercent)/sizeof(inverseFlagPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) * 100 < inverseFlagPercent[i] * PROB_FACTOR) {
                flags |= 1 << i;
            }
        }        
    }
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
    return writesz;
}
