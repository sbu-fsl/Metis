#ifndef _ABSFS_SET_H_
#define _ABSFS_SET_H_

#include "abstract_fs.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct AbsfsSet* absfs_set_t;

void absfs_set_init(absfs_set_t *set);
void absfs_set_destroy(absfs_set_t set);
int absfs_set_add(absfs_set_t set, absfs_state_t *states);
size_t absfs_set_size(absfs_set_t set);

#ifdef __cplusplus
}
#endif

#endif // _ABSFS_SET_H_
