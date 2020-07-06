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

    // accessing vector in shared memory - does not work, deallacation(?) occurs
    // this code causes a segfault
    // std::pmr::vector<char>* myVector = (std::pmr::vector<char>*)ptr;
    // std::cout << myVector -> at(0) << std::endl;
    // std::cout << "myVector addr: " << myVector << std::endl;

    // getting a - doesn't work
    void* valueAddrV1 = (std::byte*)(ptr) + 16;
    char* valueV1 = (char*) valueAddrV1;
    std::cout << "value addrV1: " << valueAddrV1 << std::endl;
    std::cout << "valueV1: " << *valueV1 << std::endl;

    // getting b - doesnt't work
    void* valueAddrV2 = (std::byte*)(ptr) + 17;
    char* valueV2 = (char*) valueAddrV2;
    std::cout << "value addrV2: " << valueAddrV2 << std::endl;
    std::cout << "valueV2: " << *valueV2 << std::endl;

    // accessing a char from the vector
    void* valueAddr = (std::byte*)(ptr) + 18;
    char* value = (char*) valueAddr;
    std::cout << "value addr: " << valueAddr << std::endl;
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