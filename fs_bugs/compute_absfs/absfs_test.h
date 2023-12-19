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

#include "abstract_fs.h"
#include <stdio.h>
#include <stdlib.h>

#ifndef _ABSFS_TEST_H
#define _ABSFS_TEST_H

char *get_abstract_state(const char *basepath, unsigned int hash_method, char *abs_state_str);

#endif // _ABSFS_TEST_H
