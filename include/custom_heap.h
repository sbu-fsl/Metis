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

#ifndef _CUSTOM_HEAP_H
#define _CUSTOM_HEAP_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

void try_init_myheap(void);
void *my_morecore(ptrdiff_t increment);
void unset_myheap(void);

#ifdef __cplusplus
}
#endif

#endif
