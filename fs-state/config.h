#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

/* This should be a multiple of N_FS
 * in order to avoid false discrepancy in open() tests */
#define MAX_OPENED_FILES 192

/* List of file systems: Modify this to experiment with other file systems */
static char *fslist[] = {"ext4", "ext2", "jffs2"};
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
static int fds[N_FS] = {-1};
int i;

#endif // _FSSTATE_CONFIG_H_
