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

#ifndef _MY_MALLOC_H_
#define _MY_MALLOC_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

//#define ALIGNMENT 4
//last three bits should be 0 for alignment
//#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x3)
#define HEADER_SIZE (sizeof(block_t*)*2+sizeof(void*)+sizeof(size_t)*2)
#define MAX_VAL(a, b)  ((a) > (b) ? (a) : (b))
#define MINSIZE 48


typedef struct mem_block{
    size_t size; /*total block size*/
    size_t free_size; /*the current free size can be allocated*/
    struct mem_block *start_brk; /*the program break BEFORE use sbrk to extend*/
    struct mem_block *end_brk; /*the program break AFTER sbrk*/
    void *curr_ptr; /*the current pointer to the free memory space*/
    char data[0];  /*payload, the first byte of data segment*/
} block_t;

extern block_t* new_block;

int malloc_init(block_t** new_block, size_t block_size);
void* my_malloc_helper(size_t size, block_t** new_block);
void *my_malloc(size_t size);
void my_free(void* ptr);
void print_new_block();

#endif