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