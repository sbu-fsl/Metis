#include "my_malloc.h"

/*
 * malloc_init is to initialize new_block (the block we used to distribute memory)
 * return 0 on success, return 1 on failure
 */
int malloc_init(block_t** new_block, size_t block_size)
{
    if (block_size <= 0){
        printf("[malloc_init] block_size error\n");
        return 1;
    }
    size_t new_size;
    new_size = MAX_VAL(block_size+HEADER_SIZE, MINSIZE);

    (*new_block) = (block_t*)sbrk(new_size);
    if((void*)*new_block == (void*)-1 || *new_block == NULL){
        printf("[malloc_init] sbrk failed\n");
        return 1;
    }
    printf("sbrk_ret: %p\n", *new_block);
    //populate new_block
    (*new_block)->start_brk = *new_block;
    (*new_block)->curr_ptr = (void*)*new_block + HEADER_SIZE;
    (*new_block)->end_brk = (block_t *)sbrk(0);
    (*new_block)->size = new_size - HEADER_SIZE;
    (*new_block)->free_size = new_size - HEADER_SIZE;
    return 0;
}


void* my_malloc_helper(size_t alloc_size, block_t** new_block)
{
    if (alloc_size > (*new_block)->free_size){
        return NULL;
    }
    void* orig_ptr = (*new_block)->curr_ptr;
    (*new_block)->curr_ptr += alloc_size;
    (*new_block)->free_size -= alloc_size;
    return orig_ptr;
}

void *my_malloc(size_t size)
{
    printf("Using my_malloc...\n");
    if (size <= 0)
    {
        return NULL;
    }
    void *ret;
    ret = my_malloc_helper(size, &new_block);
    return ret;
}


void my_free(void* ptr){
    printf("Using my_free...\n");
    if (ptr == NULL){
        return;
    }
    int brk_ret;
    brk_ret = brk(new_block->start_brk);
    if(brk_ret == -1){
        printf("brk failed\n");
        exit(EXIT_FAILURE);
    }
    new_block = NULL;
}

void print_new_block()
{
    printf("total_size=%zu\t free_size=%zu\t  start_brk=%p\t end_brk=%p\t curr_ptr=%p\t data=%d\n", 
        new_block->size, new_block->free_size, new_block->start_brk, new_block->end_brk, new_block->curr_ptr, (int)*new_block->data);
}