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
// g++ -o sender2 sender2.cpp -lrt -std=c++17 -Wall -Wextra -pedantic-errors

/*
Of note:
    -we seem to have done it (allocate the data of the vector and the vector itself)
    -I have no idea what memory is allocated for vector, which could be an issue (seemed to be 16 bytes for the vector 
    itself and 2 bytes - which we allocated - for its contents)
*/
void ShareMemoryWrite() {
    printf("Producer called (vector version 7.0)\n");

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
    
    // size of vector and offset
    int sizeVector = sizeof(std::pmr::vector<char>);
    int offsetValue = sizeVector + 2; // the extra 2 is for the chars stored in the vector
    std::cout << "size of vector is: " << sizeVector << std::endl; // see what the size of the vector object is

    // getting address of pool ptr and additional ptr
    void* offsetPool = (std::byte*)ptr + sizeVector;  // where vector data is stored
    void* offsetPtr = (std::byte*)ptr + offsetValue;  // where pointer is stored

    // size of buffer
    int sizeBuf = 2; // we will only put two chars in the vector so 2 bytes

    // creating our vector in shared memory    
    std::pmr::monotonic_buffer_resource pool(offsetPool, sizeBuf, std::pmr::null_memory_resource());
    std::pmr::vector<char>* myVector = new (ptr) std::pmr::vector<char>{{'a', 'b'}, &pool};

    // checking addresses
    std::cout << "myVector addr: " << myVector << std::endl;
    std::cout << "ptr addr: " << ptr << std::endl;
    std::cout << "offset pool addr: " << offsetPool << std::endl;
    std::cout << "offset ptr addr: " << offsetPtr << std::endl;
    
    // creating different type of ptr in shared memory
    char* myChar = (char*)offsetPtr;
    *myChar = 'c';

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
