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

#ifndef _MALLOC_HOOK_H_
#define _MALLOC_HOOK_H_

#include "my_malloc.h"

/* Prototypes for our hooks.  */
void my_init_hook (void);
void *my_malloc_hook (size_t, const void *);
void my_free_hook (void*, const void *);

#endif