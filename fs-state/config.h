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
#define FILE_COUNT 1
#define DIR_COUNT 1
#define PATH_DEPTH 1
#define MAX_PATHLEN 10
#endif

int i;

#endif // _FSSTATE_CONFIG_H_
