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

#define _XOPEN_SOURCE 500   /* See feature_test_macros(7) */
#include <ftw.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const char *ext4_fs_root = "/mnt/test-ext4-i0-s0";
const char *jfs_fs_root = "/mnt/test-jfs-i1-s0";
const char *ext4_problem_file = "/mnt/test-ext4-i0-s0/d-00/f-01";
const char *jfs_problem_file = "/mnt/test-jfs-i1-s0/d-00/f-01";

int callback(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf)
{
    if (strcmp(fpath, ext4_problem_file) == 0) {
        printf("Ext4: %s\n", fpath);
        printf("file size: %zu\n", sb->st_size);
        printf("==========\n");
    }
    else if (strcmp(fpath, ext4_fs_root) == 0) {
        printf("Ext4: %s\n", fpath);
        printf("nlink: %ld\n", sb->st_nlink);
    }
    // Process the file or directory here
    if (strcmp(fpath, jfs_problem_file) == 0) {
        printf("JFS: %s\n", fpath);
        printf("file size: %zu\n", sb->st_size);
    }
    else if (strcmp(fpath, jfs_fs_root) == 0) {
        printf("JFS: %s\n", fpath);
        printf("nlink: %ld\n", sb->st_nlink);
    }
    // Returning 0 tells nftw() to continue the traversal
    return 0; 
}

int main(int argc, char *argv[])
{   
    int ext4_res = -1, jfs_res = -1;
    // nopenfd == 10: have up to 10 files open simultaneously
    // flags == 0: no additional flags are set, and nftw() will use its default behavior
    ext4_res = nftw(ext4_fs_root, callback, 10, 0);
    if (ext4_res == -1) {
        perror("Ext4 nftw");
        exit(EXIT_FAILURE);
    }
    jfs_res = nftw(jfs_fs_root, callback, 10, 0);
    if (jfs_res == -1) {
        perror("JFS nftw");
        exit(EXIT_FAILURE);
    }

    return 0;
}
