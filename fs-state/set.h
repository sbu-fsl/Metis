/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

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
