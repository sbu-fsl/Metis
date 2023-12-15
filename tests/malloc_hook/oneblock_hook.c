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

int main(int argc, char *argv[])
{
    my_init();
    int i, n = 10;
    void* curr_ptr;
    int* arr[10];
    //apply for a large block to str
    char *str;
    curr_ptr = malloc(1000);
    str = (char*)curr_ptr;
    //printf("before str: %u\n", str);
    int *ptr;
    //occupy 20 bytes for string
    strcpy(str, "randomtextrandomtext");
    curr_ptr += 20;
    //printf("after str: %u\n", str);
    printf("String is %s\n", str);
    print_block_list();
    
    printf("NEW TESTING\n");
    ptr = (int*)(curr_ptr);

    for (i = 0; i < n; i++){
        ptr[i] = i * 10 + 1;
    }
    for (i = 0; i < n; i++){
        printf("%d, ", ptr[i]);
    }
    printf("\n");
    printf("String is %s\n", str);
    print_block_list();
    curr_ptr += sizeof(int) * n;
    for (i = 0; i < n; i++){
        arr[i] = curr_ptr;
        *arr[i] = i * 20 + 5;
        curr_ptr += sizeof(int);
    }
    for (i = 0; i < n; i++){
        printf("%d, ", *arr[i]);
    }
    printf("\n");
    print_block_list();
    return 0;
}