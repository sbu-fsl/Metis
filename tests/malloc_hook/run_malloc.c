#include "malloc_hook.h"

block_t* new_block = NULL;

int main(int argc, char *argv[])
{
    printf("0000000\n");
    my_init_hook();
    printf("1111111\n");
    size_t block_size = 1000;
    //Create a new_block with block_size
    int ret = malloc_init(&new_block, block_size);
    if(ret != 0){
        printf("Error occurs for malloc_init\n");
        exit(EXIT_FAILURE);
    }
    print_new_block();
    return 0;
}