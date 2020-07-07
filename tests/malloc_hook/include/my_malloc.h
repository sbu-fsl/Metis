#ifndef _MY_MALLOC_H_
#define _MY_MALLOC_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>

#define ALIGNMENT 4
//last three bits should be 0 for alignment
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x3)
#define HEADER_SIZE (sizeof(block_t*)*2+sizeof(size_t)+sizeof(int))
#define MAX_VAL(a, b)  ((a) > (b) ? (a) : (b))
#define MINSIZE 4


typedef struct mem_block{
    size_t block_size;
    //size_t free_size;
    struct mem_block *next;
    struct mem_block *prev;
    //void *start_brk;
    //void *curr_brk;
    int isFree;
    char data[0];  /*payload, the first byte of data segment*/
} block_t;

block_t *create_mem_block(block_t *last, size_t size);
block_t* find_free_block(block_t **last, size_t size);

void *my_malloc(size_t size);
void print_block_list();
void my_free(void* ptr);

#endif