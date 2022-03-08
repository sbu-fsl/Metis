#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include "abstract_fs.h"

#ifndef MAX_FS
#define MAX_FS    10
#endif

#ifndef FS_NAME_MAX
#define FS_NAME_MAX    10
#endif

#ifdef __cplusplus
extern "C" {
#endif

#define mem_alloc_err(...) \
    fprintf(stderr, "memory allocation failed: %s:%d:%s\n", \
        __FILE__, __LINE__, __func__, ##__VA_ARGS__);

typedef struct all_global_params {
    unsigned int _swarm_id;
    unsigned int _n_fs;
    char **fslist;
    char **fssuffix;
    char **devlist;
    size_t *devsize_kb;
    char **basepaths;
    char **testdirs;
    char **testfiles;
    void **fsimgs;
    int fsfds[MAX_FS];
    absfs_state_t absfs[MAX_FS];
    int rets[MAX_FS];
    int errs[MAX_FS];
} globals_t;

extern globals_t *globals_t_p;


unsigned int get_n_fs();
char **get_fslist();
char **get_fssuffix();
char **get_devlist();
size_t *get_devsize_kb();
char **get_basepaths();
char **get_testdirs();
char **get_testfiles();
void **get_fsimgs();

#ifdef __cplusplus
}
#endif

#endif // _INIT_GLOBALS_H_
