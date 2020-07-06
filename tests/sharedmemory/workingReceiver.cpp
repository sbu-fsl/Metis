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
// g++ -o workingReceiver workingReceiver.cpp -lrt -std=c++17 -Wall -Wextra -pedantic-errors

void ShareMemoryRead() {
    printf("Consumer called (vector version)\n");

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

    // keeping our addr fine, using a pointer to obtain our ints
    int* value = (int*)ptr;
    std::cout << "ptr works" << std::endl;

    // read from the shared memory object
    printf("%d\n", value[0]); // 1 as expected
    printf("%d\n", value[1]); // 2 as expected
    printf("%d\n", value[2]); // 3 as expected
    printf("%d\n", value[3]); // 4 as expected
    printf("%d\n", value[4]); // gives 0 b/c std::vector on stack goes to trouble of setting ints to 0
    printf("%d\n", value[1023]); // gives 0 b/c std::vector on stack goes to trouble of setting ints to 0
    printf("%d\n", value[4000]); // gives 0 b/c std::vector on stack goes to trouble of setting ints to 0
    std::cout << "reading from ptr works" << std::endl;

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