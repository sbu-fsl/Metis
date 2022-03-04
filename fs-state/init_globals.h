#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include "abstract_fs.h"

#ifdef __cplusplus
extern "C" {
#endif

#define MAX_FS 10
typedef struct all_global_params {
    unsigned int _n_fs;
    char *fslist[MAX_FS];
    char *fssuffix[MAX_FS];
    char *devlist[MAX_FS];
    size_t devsize_kb[MAX_FS];
    char *basepaths[MAX_FS];
    char *testdirs[MAX_FS];
    char *testfiles[MAX_FS];
    void *fsimgs[MAX_FS];
    int fsfds[MAX_FS];
    absfs_state_t absfs[MAX_FS];
    int rets[MAX_FS];
    int errs[MAX_FS];
} globals_t;

extern globals_t *globals_t_p;

void init_all_globals();
void free_all_globals();

unsigned int get_n_fs();

#ifdef __cplusplus
}
#endif

#endif // _INIT_GLOBALS_H_
