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

#define VERIFS_AFFIX       "verifs"
#define NOVA_NAME           "nova"
#define NFS_GANESHA_EXT4_NAME  "nfs-ganesha-ext4"
#define NFS_NAME            "nfs"
#define BTRFS_NAME          "btrfs"
#define XFS_NAME            "xfs"
#define VERIFS1_NAME        "verifs1"
// #define VERIFS2_NAME        "verifs2"
#define NILFS2_NAME         "nilfs2"
#define NFS_GANESHA_EXT4_NAME_LEN  (sizeof(NFS_GANESHA_EXT4_NAME) - 1)
#define NFS_GANESHA_EXPORT_PATH "/mnt/test-nfs-ganesha-export"
#define NFS_GANESHA_LOCALHOST "127.0.0.1"
#define NFS_GANESHA_EXPORT_ID 77

static inline bool is_verifs(const char *fsname)
{
    return (strstr(fsname, VERIFS_AFFIX) != NULL);
}

static inline bool is_nova(const char *fsname)
{
    return strcmp(fsname, NOVA_NAME) == 0;
}

static inline bool is_nfs_ganesha_ext4(const char *fsname)
{
    return strncmp(fsname, NFS_GANESHA_EXT4_NAME, NFS_GANESHA_EXT4_NAME_LEN) == 0;
}

void setup_filesystems();
int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode);

int execute_cmd_status(const char *cmd);
int start_nfs_ganesha_server(int idx);

#endif // _SETUP_H_
