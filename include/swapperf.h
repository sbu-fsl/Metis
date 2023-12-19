/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#ifndef _SWAP_PERF_H_
#define _SWAP_PERF_H_

struct iostat {
    int major;
    int minor;
    bool _malloced_name;
    char *devname;
    size_t reads_success;
    size_t reads_merged;
    size_t bytes_read;
    size_t time_read;
    size_t writes_complete;
    size_t writes_merged;
    size_t bytes_written;
    size_t time_write;
    size_t io_progress;
    size_t time_io;
};

void iostat_diff(struct iostat *diff, struct iostat *a, struct iostat *b);
const char *nextfield(const char *line, char **fieldbuf, size_t *fieldlen);
void get_swapstats(struct iostat *stats);
void put_swapstats(struct iostat *stats);
int num_swap_devices();
void get_swaps();

#endif // _SWAP_PERF_H_
