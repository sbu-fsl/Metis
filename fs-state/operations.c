#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>

int create_file(const char *path, int flags, int mode)
{
    int fd = open(path, flags | O_CREAT, mode);
    int err = errno;
    if (fd >= 0) {
        close(fd);
    }
    errno = err;
    return (err == 0) ? 0 : -1;
}

int write_file(const char *path, void *data, off_t offset, size_t length)
{
    int fd = open(path, O_RDWR);
    int err;
    if (fd < 0) {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit_err;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return 0;

exit_err:
    close(fd);
    errno = err;
    return -1;
}
