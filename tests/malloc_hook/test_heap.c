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

#include "my_malloc.h"

int main()
{
    block_t *block = NULL;
    int *malloc_res;
    block = create_mem_block(NULL, 32);
    block->prev = NULL;
    malloc_res = (int*)((void*)block + HEADER_SIZE);
    malloc_res[0] = 10;
    malloc_res[1] = 20;
    printf("create_mem_block return value is %p\n", block);
    printf("malloc_res value are %d, %d\n",malloc_res[0],malloc_res[1]);
    return 0;
}