#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

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

/* List of file systems: Modify this to experiment with other file systems */
#ifndef CONFIG
static const char *fslist[] = {"ext4", "jffs2"};
static const char *fssuffix[] = {"", ""};
static const char *devlist[] = {"/dev/ram0", "/dev/mtdblock0"};
#else
#ifndef STR
#define STR_(n) #n
#define STR(n) STR_(n)
#define I1 (CONFIG*2-2)
#define I2 (CONFIG*2-1)
#endif
static const char *fslist[] = {"ext4", "ext2"};
static const char *fssuffix[] = {"-" STR(I1), "-" STR(I2)};
static const char *devlist[] = {"/dev/ram" STR(I1), "/dev/ram" STR(I2)};
#endif
static const size_t devsize_kb[] = {256, 256};
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
