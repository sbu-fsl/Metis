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
// g++ -o workingSender workingSender.cpp -lrt -std=c++17 -Wall -Wextra -pedantic-errors

void ShareMemoryWrite() {
    printf("Producer called (vector version)\n");

    // size (in bytes) of shared memory object - page size in this case
    const int SIZE = 4096;

    // name of shared memory object
    const char* name = "OS";

    // double check length of file
    off_t length;

    // shared memory file descriptior
    int shm_fd;

    // pointer to shared memory object
    void* ptr;

    // creating the shared memory object
    shm_fd = shm_open(name, O_CREAT | O_RDWR, 0666);
    if (shm_fd < 0) {
        perror("shm_open failure\n"); // prints a descriptive error message to stderr
        exit(errno);
    }

    // configure the size of the shared memory object
    if ((ftruncate(shm_fd, SIZE)) == -1) {
        perror("ftruncate failure\n");
        exit(errno);
    }

    // checks length of file using lseek/printf
    length = lseek(shm_fd, 0, SEEK_END);
    printf("Length of file: %ld\n", length);

    // memory map the shared memory object
    ptr = mmap(0, SIZE, PROT_WRITE, MAP_SHARED, shm_fd, 0);
    if (ptr == MAP_FAILED) {
        perror("mmap failed\n");
        exit(errno);
    }
    std::cout << "ptr addr immediately: " << ptr << std::endl;

    

    // trying to write with vectors
    std::pmr::monotonic_buffer_resource pool(ptr, 16, std::pmr::null_memory_resource());
    std::pmr::vector<int> myVector{{1,2,3,4}, &pool};
    std::cout << "Myvector addr: " << &myVector << std::endl; 
    std::cout << "pool addr: " << &pool << std::endl;   
    std::cout << "ptr addr: " << ptr << std::endl;

    // removes mappins
    if (munmap(ptr, SIZE) != 0) {
        perror("munmap failed\n");
        exit(errno);
    }

    // closes our file
    close(shm_fd);

    std::cout << std::endl;
}

int main()
{    
    ShareMemoryWrite();
}