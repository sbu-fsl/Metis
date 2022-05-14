#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

int write_file(const char *path, off_t offset, size_t length, int byte)
{
    int ret = -1, err = -1;
    int fd = open(path, O_RDWR);
    if (fd < 0) {
        return ret;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit;
    }

    char *data = malloc(length);
    if (data == NULL) {
        err = errno;
        goto exit;
    }
    memset(data, byte, length);

    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    ret = writesz;

exit:
    close(fd);
    errno = err;
    return ret;
}

int main(int argc, void **argv)
{
    char *file = argv[1];
    int offset = atoi(argv[2]);
    int len = atoi(argv[3]);
    int byte = atoi(argv[4]);

    int ret = write_file(file, offset, len, byte);
    if (ret == -1) {
        perror("Error while writing to file\n");
    }
    return ret;
}
