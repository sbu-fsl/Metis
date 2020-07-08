#include "malloc_hook.h"

block_t* new_block = NULL;

int main(int argc, char *argv[])
{
    /* Initialization */
    printf("Start of run_malloc...\n");
    my_init_hook();
    printf("Init hook finished\n");
    size_t block_size = 100;
    //Create a new_block with block_size by malloc_init()
    int ret = malloc_init(&new_block, block_size);
    if(ret != 0){
        printf("Error occurs for malloc_init\n");
        exit(EXIT_FAILURE);
    }
    print_new_block();

    /* allocate memory for first variable: a 20-length str */
    char* str;
    str = (char*)malloc(25);
    if(str == NULL){
        printf("[str] No enough space, EXIT...\n");
        print_new_block();
        exit(EXIT_FAILURE);
    }
    strcpy(str, "randomtextrandomtext");
    printf("String is %s\n", str);
    print_new_block();

    /* allocate memory for second variable: an integer array */
    const int N = 10;
    int i;
    int* arr[N];
    for (i = 0; i < N; i++){
        arr[i] = malloc(sizeof(int));
        if (arr[i] == NULL){
            printf("[arr] No enough space, EXIT...\n");
            print_new_block();
            exit(EXIT_FAILURE);
        }
        else{
            *arr[i] = i * 10 + 5;
            printf("arr: %d\n", *arr[i]);
        }
    }
    print_new_block();
    return 0;
}