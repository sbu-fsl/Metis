#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

/* This should be a multiple of N_FS
 * in order to avoid false discrepancy in open() tests */
#define MAX_OPENED_FILES 192
/* The file name of or the path to the performance log */
#define PERF_LOG_PATH    "perf1.csv"
/* The name of or the path to the logs (without .log suffix) */
#define SEQ_LOG_PATH     "sequence1"
#define OUTPUT_LOG_PATH  "output1"
#define ERROR_LOG_PATH   "error1"
/* Interval of perf metrics logging (in secs) */
#define PERF_INTERVAL    5
/* Max length of function name in log */
#define FUNC_NAME_LEN    16
/* Abort the whole program when expect() fails */
#define ABORT_ON_FAIL    1

/* List of file systems: Modify this to experiment with other file systems */
static const char *fslist[] = {"ext2", "ext4"};
static const char *fssuffix[] = {"-0", "-1"};
static const char *devlist[] = {"/dev/ram0", "/dev/ram1"};
#define N_FS    nelem(fslist)
char *basepaths[N_FS];
char *testdirs[N_FS];
char *testfiles[N_FS];

/* Pointer to memory-mapped file system images */
void *fsimgs[N_FS];
/* File descriptors of the opened f/s images */
int fsfds[N_FS];

absfs_state_t absfs[N_FS];

FILE *seqfp;

int rets[N_FS], errs[N_FS];
int i;

#endif // _FSSTATE_CONFIG_H_