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
#define NFS_GANESHA_VERIFS2_NAME  "nfs-ganesha-verifs2"
#define NFS_GANESHA_NAME    "nfs-ganesha"
#define NFS_NAME            "nfs"
#define BTRFS_NAME          "btrfs"
#define XFS_NAME            "xfs"
#define VERIFS1_NAME        "verifs1"
// #define VERIFS2_NAME        "verifs2"
#define NILFS2_NAME         "nilfs2"
/* NFS-Ganesha macros */
#define NFS_GANESHA_EXPORT_PATH "/mnt/test-nfs-ganesha-export"
#define NFS_GANESHA_LOCALHOST "127.0.0.1"
#define NFS_GANESHA_EXPORT_ID 77
/* Kernel NFS macros */
#define NFS_EXT4_NAME  "nfs-ext4"
#define NFS_EXPORT_PATH "/mnt/test-nfs-export"
#define NFS_ROOT_EXPORT_PATH "/"
#define NFS_LOCALHOST "localhost"
#define NFS_VERIFS2_NAME "nfs-verifs2"

/* Check if "verifs" is a substring, which checks verifs1,
 * verifs2, nfs-ganesha-verifs2, nfs-verifs2, etc. 
 */
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
    return strncmp(fsname, NFS_GANESHA_EXT4_NAME, strlen(NFS_GANESHA_EXT4_NAME)) == 0;
}

static inline bool is_nfs_ganesha(const char *fsname)
{
    return strncmp(fsname, NFS_GANESHA_NAME, strlen(NFS_GANESHA_NAME)) == 0;
}

static inline bool is_nfs_ganesha_verifs2(const char *fsname) {
    return strncmp(fsname, NFS_GANESHA_VERIFS2_NAME, strlen(NFS_GANESHA_VERIFS2_NAME)) == 0;
}

static inline bool is_nfs_ext4(const char *fsname)
{
    return strncmp(fsname, NFS_EXT4_NAME, strlen(NFS_EXT4_NAME)) == 0;
}

static inline bool is_nfs_verifs2(const char *fsname) {
    return strncmp(fsname, NFS_VERIFS2_NAME, strlen(NFS_VERIFS2_NAME)) == 0;

}

void setup_filesystems();
int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode);

int execute_cmd_status(const char *cmd);
int start_nfs_ganesha_server(int idx);
int export_nfs_server(int idx);

#endif // _SETUP_H_
