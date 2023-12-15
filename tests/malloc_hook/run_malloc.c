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
    printf("\n");
    char* str;
    str = (char*)malloc(21);
    if(str == NULL){
        printf("[str] No enough space, EXIT...\n");
        print_new_block();
        exit(EXIT_FAILURE);
    }
    strcpy(str, "randomtextrandomtext");
    printf("String is %s\n", str);
    print_new_block();

    /* allocate memory for second variable: an integer array */
    printf("\n");
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
        }
    }
    for (i = 0; i < N; i++){
        printf("%d ", *arr[i]);
    }
    printf("\n");
    print_new_block();

    /* Free this memory block except header*/
    printf("\n");
    free((void*)new_block->start_brk + HEADER_SIZE);
    return 0;
}