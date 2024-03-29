/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Alex Bishka
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include <vector>
#include <iostream>
#include <cstddef>
#include <limits>
#include <memory_resource>
#include <stdio.h>
#include <stdlib.h> 
#include <string.h> 
#include <fcntl.h> 
#include <sys/shm.h> 
#include <sys/mman.h>
#include <sys/stat.h> 
#include <unistd.h>
#include <sys/types.h>
#include <errno.h>

// to compile/run: 
// g++ -o receiver receiver.cpp -lrt -std=c++17 -Wall -Wextra -pedantic-errors

void ShareMemoryRead() {
    printf("Consumer called (vector version 7.0)\n");

    // size (in bytes) of shared memory object
    const int SIZE = 4096;

    // name of shared memory object
    const char* name = "OS";

    // shared memory file descriptior
    int shm_fd;

    // pointer to shared memory object
    void* ptr;

    // creating the shared memory object
    shm_fd = shm_open(name, O_RDONLY, 0666);

    // memory map the shared memory object
    ptr = mmap(0, SIZE, PROT_READ, MAP_SHARED, shm_fd, 0); 
    if (ptr == MAP_FAILED) {
        perror("mmap failed\n");
        exit(errno);
    }
    
    // address of ptr
    std::cout << "addr ptr from mmap: " << ptr << std::endl;

    // size of vector and offset
    int sizeVector = sizeof(std::pmr::vector<char>);
    int offsetValue = sizeVector + 2;

    // getting address of pool ptr and additional ptr
    void* offsetPool = (std::byte*)ptr + sizeVector;  // where vector data is stored
    void* offsetPtr = (std::byte*)ptr + offsetValue;  // where pointer is stored

    // accessing vector in shared memory - does not work, deallacation(?) occurs
    // this code causes a segfault
    // std::pmr::vector<char>* myVector = (std::pmr::vector<char>*)ptr;
    // std::cout << myVector -> at(0) << std::endl;
    // std::cout << "myVector addr: " << myVector << std::endl;

    // getting a - does work this time
    char* valueV1 = (char*) offsetPool;
    std::cout << "addr pool: " << offsetPool << std::endl;
    std::cout << "valueV1: " << *valueV1 << std::endl;

    // accessing other char ptr
    char* value = (char*) offsetPtr;
    std::cout << "addr additional ptr: " << offsetPtr << std::endl;
    std::cout << "value: " << *value << std::endl;

    // removes mappings
    if (munmap(ptr, SIZE) != 0) {
        perror("munmap failed\n");
        exit(errno);
    }

    // closes our file
    close(shm_fd);

    // remove the shared memory object
    shm_unlink(name);
}

int main() {
    ShareMemoryRead();
}