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
#include <sys/ioctl.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>

// #define SHELL_MOUNT 1

/* 
 * Here we set at most 100 cycles. 
 * Change it to a larger value if you cannot reproduce the kernel crash
 */
#define LOOP_MAX 100

char *ftfs_mp = NULL;
char *ftfs_dev = NULL;
char *ftfs_name = NULL;

#ifdef SHELL_MOUNT
static int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}
#endif

int main(int argc, char *argv[])
{
    if (argc < 4) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <fs-type>\n", argv[0]);
        exit(1);
    }

    ftfs_mp = argv[1];
    ftfs_dev = argv[2];
    ftfs_name = argv[3];

    int cur_loop = 0;
    while (cur_loop < LOOP_MAX) {
	    fprintf(stdout, "Current loop: %d out of %d\n", cur_loop + 1, LOOP_MAX);
        int ret = -1;
#ifndef SHELL_MOUNT
        /* Mount ftfs by mount(2) syscall */
        ret = mount(ftfs_dev, ftfs_mp, ftfs_name, MS_NOATIME, "");
        if (ret != 0) {
            fprintf(stderr, "Failed to Mount ftfs: Error %s\n", strerror(errno));
        }
        else {
            fprintf(stdout, "BetrFS Mount succeeded.\n");
        }
#else
        /* Mount ftfs by mount shell command */
        char cmdbuf[PATH_MAX];
        snprintf(cmdbuf, PATH_MAX,
                    "mount -t ftfs %s %s -o max=%d",
                    ftfs_dev,
                    ftfs_mp,
                    128);
        if (execute_cmd_status(cmdbuf) == 0) {
            fprintf(stdout, "BetrFS mount succeeded.\n");
        }
        else {
            fprintf(stderr, "Failed to mount ftfs: Error %s\n", strerror(errno));
            exit(1);
        }
#endif
        ret = -1;
        ret = umount2(ftfs_mp, 0);
        if (ret != 0) {
            fprintf(stderr, "Failed to Unmount ftfs: Error %s\n", strerror(errno));
        }
        else {
            fprintf(stdout, "BetrFS Unmount succeeded.\n");
        }
        ++cur_loop;
    }
    return 0;
}
