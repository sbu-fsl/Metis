#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

/* write to path, at offset, for len bytes, value "byte" */
int main(int argc, char *argv[])
{
    char *path = argv[1];
    int offset = atoi(argv[2]);
    ssize_t len = atoi(argv[3]);
    int byte = atoi(argv[4]);

    int fd = open(path, O_RDWR|O_CREAT);
    if (fd < 0) {
      perror(path);
      exit(1);
    }

    off_t res = lseek(fd, offset, SEEK_SET);
    if (res < 0) {
      perror("lseek");
      exit(1);
    }

    char *data = malloc(len);
    if (data == NULL) {
      errno = ENOMEM;
      perror("malloc");
      exit(1);
    }
    memset(data, byte, len);

    ssize_t writesz = write(fd, data, len);
    if (writesz < 0) {
      perror("write");
      exit(1);
    }
    if (writesz < len) {
      fprintf(stderr, "Note: less data written than expected (%ld < %ld)\n",
	      writesz, len);
      exit(1);
    }

    close(fd);
    exit(0);
}
