/*
 * Copyright (c) 2020-2023 Yifei Liu
 * Copyright (c) 2020-2023 Wei Su
 * Copyright (c) 2020-2023 Erez Zadok
 * Copyright (c) 2020-2023 Stony Brook University
 * Copyright (c) 2020-2023 The Research Foundation of SUNY
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
