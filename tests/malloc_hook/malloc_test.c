#include "malloc_hook.h"

block_t new_block;

int main(int argc, char *argv[])
{
    my_init_hook();
    int block_size = 1000;
    //Create a new_block with block_size
    int ret = malloc_init(&new_block, block_size);
    if(ret != 0){
        printf("Error occurs for malloc_init\n");
        exit(EXIT_FAILURE);
    }
    return 0;
}