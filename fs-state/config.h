#ifndef _FSSTATE_CONFIG_H_
#define _FSSTATE_CONFIG_H_

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

/* This should be a multiple of N_FS
 * in order to avoid false discrepancy in open() tests */
#define MAX_OPENED_FILES 192

static char *fslist[] = {"xfs", "jffs2"};
#define n_fs    nelem(fslist)
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

void *fsimg_ext4, *fsimg_ext2, *fsimg_jffs2, *fsimg_xfs;
int fsfd_ext4, fsfd_ext2, fsfd_jffs2, fsfd_xfs;
absfs_state_t absfs[n_fs];

FILE *seqfp;

int rets[n_fs], errs[n_fs];
static int fds[n_fs] = {-1};
int i;

#endif // _FSSTATE_CONFIG_H_
