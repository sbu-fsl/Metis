#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

/* This should be a multiple of N_FS
 * in order to avoid false discrepancy in open() tests */
#define MAX_OPENED_FILES 192
/* The file name of or the path to the performance log */
#define PERF_LOG_PATH    "perf.csv"
/* The file name of or the path to the sequence log */
#define SEQ_LOG_PATH     "sequence.log"
/* Interval of perf metrics logging (in secs) */
#define PERF_INTERVAL    5
/* Max length of function name in log */
#define FUNC_NAME_LEN    16
/* Abort the whole program when expect() fails */
#define ABORT_ON_FAIL    1

/* List of folders to be excluded */
static const char *exclude_dirs[] = {"lost+found", NULL};
/* List of file systems: Modify this to experiment with other file systems */
static const char *fslist[] = {"ext4", "ext2", "jffs2"};
static const char *devlist[] = {"/dev/ram0", "/dev/ram1", "/dev/mtdblock0"};
#define N_FS    nelem(fslist)
char *basepaths[N_FS];
char *testdirs[N_FS];
char *testfiles[N_FS];

/* Modify those to experiment with other file systems */
/* Pointer to memory-mapped file system images */
void *fsimg_ext4, *fsimg_ext2, *fsimg_jffs2;
/* File descriptors of the opened f/s images */
int fsfd_ext4, fsfd_ext2, fsfd_jffs2;

absfs_state_t absfs[N_FS];

FILE *seqfp;

int rets[N_FS], errs[N_FS];
int i;

#endif // _FSSTATE_CONFIG_H_
