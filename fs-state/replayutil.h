/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Divyaank Tiwari
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#ifndef _REPLAY_H_
#define _REPLAY_H_

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/mount.h>
#include <sys/xattr.h>
#include <limits.h>

// This flag governs whether replayer uses Checkpoint/Restore (1) or not (0) during its execution
// By default Checkpoint/Restore is disabled as it causes memory leak while replaying large sequence of operations
#define ENABLE_REPLAYER_CR 0

#define __USE_XOPEN_EXTENDED 1
#include <ftw.h>

#include "vector.h"

#include "errnoname.h"
#include "fileutil.h" // includes "abstract_fs.h"
#include "operations.h"

#define ABSFS_STR_LEN 33

typedef struct concrete_state {
	int seqid;
	char **images;
} fs_state_t;

void extract_fields(vector_t *fields_vec, char *line, const char *delim);
void destroy_fields(vector_t *fields_vec);
int do_create_file(vector_t *argvec);
int do_write_file(vector_t *argvec, int seq);
int do_truncate(vector_t *argvec);
int do_unlink(vector_t *argvec);
int do_mkdir(vector_t *argvec);
int do_rmdir(vector_t *argvec);
int do_rename(vector_t *argvec);
int do_symlink(vector_t *argvec);
int do_link(vector_t *argvec);
int do_setxattr(vector_t *argvec);
int do_removexattr(vector_t *argvec);
int do_chown(vector_t *argvec);
int do_chgrp(vector_t *argvec);
int do_chmod(vector_t *argvec);
void populate_replay_basepaths();
void replayer_init(vector_t states);
void checkpoint(int seq, vector_t states);
void restore(vector_t states);
char *get_replayed_absfs(const char *basepath, unsigned int hash_method, char *abs_state_str);
void execute_cmd(const char *cmd);

#endif

