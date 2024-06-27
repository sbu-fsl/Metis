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

#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

/* This should be a multiple of N_FS
 * in order to avoid false discrepancy in open() tests */
#define MAX_OPENED_FILES 192
/* The file name of or the path to the performance log */
#define PERF_PREFIX      "perf"
/* The name of or the path to the logs (without .log suffix) */
#define SEQ_PREFIX       "sequence"
#define OUTPUT_PREFIX    "output"
#define ERROR_PREFIX     "error"
/* Interval of perf metrics logging (in secs) */
#define PERF_INTERVAL    5
/* Max length of function name in log */
#define FUNC_NAME_LEN    16
/* Abort the whole program when expect() fails */
#define ABORT_ON_FAIL    1

/* File/Dir Pool Related Configurations */
#ifdef FILEDIR_POOL
#define FILE_COUNT 3
#define DIR_COUNT 2
#define PATH_DEPTH 2
#define MCFS_NAME_LEN 4
#endif

/* Probabilities to select files/dirs in the promela driver 
 * By default, use 0.95 for all the followings */
#define CHMOD_FILE_PROB 0.95
#define CHOWN_FILE_PROB 0.95
#define CHGRP_FILE_PROB 0.95
#define RENAME_FILE_PROB 0.95
#define SYMLINK_FILE_PROB 0.95

#endif // _FSSTATE_CONFIG_H_
