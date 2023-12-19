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
#include <sys/xattr.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <openssl/md5.h>

#include "nanotiming.h"
#include "operations.h"
#include "errnoname.h"
#include "vector.h"
#include "abstract_fs.h"
#include "set.h"
#include "log.h"
#include "init_globals.h"
#ifdef CBUF_IMAGE
#include "circular_buf.h"
#endif

#ifndef _SETUP_H_
#define _SETUP_H_

#define VERIFS_PREFIX       "veri"
#define BTRFS_NAME          "btrfs"
#define XFS_NAME            "xfs"
#define VERIFS1_NAME        "verifs1"
#define NILFS2_NAME         "nilfs2"
#define VERIFS_PREFIX_LEN   (sizeof(VERIFS_PREFIX) - 1)

static inline bool is_verifs(const char *fsname)
{
    return strncmp(fsname, VERIFS_PREFIX, VERIFS_PREFIX_LEN) == 0;
}

void setup_filesystems();
int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode);

#endif // _SETUP_H_
