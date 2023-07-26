#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include "config.h"
#include "abstract_fs.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifndef MAX_FS
#define MAX_FS      20
#endif

#define ENV_KEY_MAX 20

#ifndef MAX_DIR_NUM
#define MAX_DIR_NUM 200
#endif

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

#define mem_alloc_err(...) \
    do { \
        fprintf(stderr, "memory allocation failed: %s:%d:%s\n", \
            __FILE__, __LINE__, __func__, ##__VA_ARGS__); \
        exit(EXIT_FAILURE); \
    } while(0)

typedef struct all_dev_nums {
    int all_rams;
    int all_mtdblocks;
} dev_nums_t;

static const char *fs_all[] = {"btrfs", "ext2", "ext4", "f2fs", 
                               "jffs2", "ramfs", "tmpfs", "verifs1", 
                               "verifs2", "xfs", "nilfs2", "jfs"};
                               
static const char *dev_all[]= {"ram", "ram", "ram", "ram", 
                                "mtdblock", "", "", "", 
                                "", "ram", "ram", "ram"};
#define ALL_FS nelem(fs_all)

static inline int get_dev_from_fs(char *fs_type) {
    int ret = -1;
    for (int i = 0; i < ALL_FS; ++i) {
        if (strcmp(fs_type, fs_all[i]) == 0) 
            return i;
    }
    return ret;
}

#ifdef FILEDIR_POOL
static inline bool is_prefix(const char *pre, const char *str)
{
    if (strlen(pre) > strlen(str))
        return false;
    return strncmp(pre, str, strlen(pre)) == 0;
}
#endif

typedef struct all_global_params {
    int _swarm_id;
    unsigned int _n_fs;
    char **fslist;
    char **fssuffix;
    char **devlist;
    size_t *devsize_kb;
    char **basepaths;
    char **testdirs;
    char **testfiles;
    void **fsimgs;
    int *fsfds;
    absfs_state_t *absfs;
    int *rets;
    int *errs;
    /* Fields related to new operations and dir structure */
    int fpoolsize;
    int dpoolsize;
    char ***filepool; // number of file systems -> size of file pool -> each file pathname
    char ***directorypool;
    /* Fields on xattr */
    char **xfpaths;
} globals_t;

extern globals_t *globals_t_p;
extern bool *fs_frozen;

static inline unsigned int get_n_fs() {
    return globals_t_p->_n_fs;
}

static inline char **get_fslist() {
    return globals_t_p->fslist;
}

static inline char **get_fssuffix() {
    return globals_t_p->fssuffix;
}

static inline char **get_devlist() {
    return globals_t_p->devlist;
}

static inline size_t *get_devsize_kb() {
    return globals_t_p->devsize_kb;
}

static inline char **get_basepaths() {
    return globals_t_p->basepaths;
}

static inline char **get_testdirs() {
    return globals_t_p->testdirs;
}

static inline char **get_testfiles() {
    return globals_t_p->testfiles;
}

static inline void **get_fsimgs() {
    return globals_t_p->fsimgs;
}

static inline int *get_fsfds() {
    return globals_t_p->fsfds;
}

static inline absfs_state_t *get_absfs() {
    return globals_t_p->absfs;
}

static inline int *get_rets() {
    return globals_t_p->rets;
}

static inline int *get_errs() {
    return globals_t_p->errs;
}

static inline int get_fpoolsize() {
    return globals_t_p->fpoolsize;
}

static inline int get_dpoolsize() {
    return globals_t_p->dpoolsize;
}

static inline char ***get_filepool() {
    return globals_t_p->filepool;
}

static inline char ***get_directorypool() {
    return globals_t_p->directorypool;
}

static inline char **get_xfpaths() {
    return globals_t_p->xfpaths;
}

#ifdef FILEDIR_POOL
extern char **bfs_fd_pool;
extern int combo_pool_idx;
#endif

#ifdef __cplusplus
}
#endif

#endif // _INIT_GLOBALS_H_
