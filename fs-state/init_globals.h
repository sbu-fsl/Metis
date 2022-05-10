#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
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

static const char *fs_all[] = {"btrfs", "ext2", "ext4", "f2fs",    "jffs2", "ramfs", "tmpfs", "verifs1", "verifs2", "xfs"};
static const char *dev_all[]= {  "ram",  "ram",  "ram",  "ram", "mtdblock",      "",      "",        "",        "", "ram"};
#define ALL_FS    nelem(fs_all)

static inline int get_dev_from_fs(char *fs_type) {
    int ret = -1;
    for (int i = 0; i < ALL_FS; ++i) {
        if (strcmp(fs_type, fs_all[i]) == 0) 
            return i;
    }
    return ret;
}

static inline bool is_prefix(const char *pre, const char *str)
{
    if (strlen(pre) > strlen(str))
        return false;
    return strncmp(pre, str, strlen(pre)) == 0;
}

typedef struct all_global_params {
    int _swarm_id;
    unsigned int _n_fs;
    char **fslist;
    char **fssuffix;
    char **devlist;
    size_t *devsize_kb;
    char **basepaths;
    char **testdirs;
    char **testdirs_dst;
    char **testfiles;
    char **testfiles_dst;
    void **fsimgs;
    int *fsfds;
    absfs_state_t *absfs;
    int *rets;
    int *errs;
    /* Fields related to new operations and dir structure */
    int filecount;
    int directorycount;
    int filepool_idx;
    int dirpool_idx;
    int path_depth;
    int max_name_len;
    char **filepool;
    char **directorypool;
} globals_t;

extern globals_t *globals_t_p;
extern bool *fs_frozen;

unsigned int get_n_fs();
char **get_fslist();
char **get_fssuffix();
char **get_devlist();
size_t *get_devsize_kb();
char **get_basepaths();
char **get_testdirs();
char **get_testdirs_dst();
char **get_testfiles();
char **get_testfiles_dst();
void **get_fsimgs();
int *get_fsfds();
absfs_state_t *get_absfs();
int *get_rets();
int *get_errs();
int get_filecount();
int get_directorycount();
int get_filepool_idx();
int get_dirpool_idx();
int get_pool_depth();
int get_max_name_len();
char **get_filepool();
char **get_directorypool();

#ifdef __cplusplus
}
#endif

#endif // _INIT_GLOBALS_H_
