#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

/* Read file with offset and dump the read buffer */
int main(int argc, char *argv[])
{
    char *path = argv[1];
    int offset = atoi(argv[2]);
    ssize_t cnt = atoi(argv[3]);
    const size_t bs = 4096;
    char buf[bs];

    int fd = open(path, O_RDONLY);
    if (fd < 0) {
        perror(path);
        exit(1);
    }

    off_t res = lseek(fd, offset, SEEK_SET);
    if (res < 0) {
      perror("lseek");
      exit(1);
    }

    int rbytes = read(fd, buf, bs);
    if (rbytes <= 0) {
      perror("read");
      exit(1);
    }

    for (int i = 0; i < cnt; ++i) {
        printf("%02x ", buf[i]);
        if ((i + 1) % 16 == 0) 
            printf("\n");
    }
    printf("\n");

    close(fd);
    exit(0);
}
