/*
 * Copyright (c) 2020-2023 Yifei Liu
 * Copyright (c) 2020-2023 Wei Su
 * Copyright (c) 2020-2023 Erez Zadok
 * Copyright (c) 2020-2023 Stony Brook University
 * Copyright (c) 2020-2023 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <sys/vfs.h>
#include <zlib.h>
#include "operations.h"

#ifndef _FSTESTUTIL_H
#define _FSTESTUTIL_H

#define min(x, y) ((x >= y) ? y : x)

#define SYSCALL_NUM 6
#define BUF_SIZE 4096
typedef unsigned char crc32_state_t[4];

static inline void generate_test_data(char *buffer, size_t len, int value)
{
    if (value > 0) {
        memset(buffer, value, len);
    } else {
        size_t i = 0, remaining = len;
        int n = rand();
        while (remaining > 0) {
            int *ptr = (int *)(buffer + i);
            *ptr = n;
            remaining -= min(sizeof(int), remaining);
            i += min(sizeof(int), remaining);
        }
    }
}

/* Return a random number [lower, upper] */
static inline int getRandNum(int lower, int upper)
{
    return (rand() % (upper - lower + 1)) + lower;
}

int randSyscall(int ops_num, char *test_file, char *test_dir);
int randSyscallChanger(int ops_num, char *test_file, char *test_dir, bool *changed);
void execute_cmd(const char *cmd);
void file_CRC32(char *file_path, crc32_state_t *crc32_hash);

#endif // _FSTESTUTIL_H