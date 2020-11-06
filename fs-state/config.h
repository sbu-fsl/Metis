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
/* Abort the model checking process as soon as the file system is corrupted */
#define ABORT_ON_BADFS   1

/* List of file systems: Modify this to experiment with other file systems */
static char *fslist[] = {"xfs", "jffs2"};
#define N_FS    nelem(fslist)
char *basepaths[N_FS];
char *testdirs[N_FS];
char *testfiles[N_FS];

/* Modify those to experiment with other file systems */
/* Pointer to memory-mapped file system images */
void *fsimg_jffs2, *fsimg_xfs;
/* File descriptors of the opened f/s images */
int fsfd_jffs2, fsfd_xfs;

absfs_state_t absfs[N_FS];

FILE *seqfp;

int rets[N_FS], errs[N_FS];
static int fds[N_FS] = {-1};
int i;

#endif // _FSSTATE_CONFIG_H_
