#define _GNU_SOURCE
#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

int create_file(const char *path, int flags, int mode)
{
    int fd = open(path, flags, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length)
{
    int fd = open(path, flags, O_RDWR);
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
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int fallocate_file(const char *path, off_t offset, off_t len)
{
    int fd = open(path, O_RDWR);
    int err;
    int ret = -1;
    if (fd < 0) {
        err = errno;
        return -1;
    }
    ret = fallocate(fd, 0, offset, len);
    if (ret < 0) {
        err = errno;
        goto exit_err;
    }
    close(fd);
    return ret;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int chown_file(const char *path, uid_t owner)
{
    return chown(path, owner, -1);
}

int chgrp_file(const char *path, gid_t group)
{
    return chown(path, -1, group);
}

static int pick_driver_open_flags()
{
    int flags = 0;
    // TODO: maybe call this srand only once at the beginning
    srand(time(0));
    if (IS_UNIFORM_FLAG) {
        for (int i = 0; i < MAX_FLAG_BITS; i++) {
            // [0, 1) (i.e., up to but not including 1)
            if ((double)rand() / (RAND_MAX) < UNIFORM_FLAG_RATE) {
                flags |= 1 << i;
            }
        }
    }
    else {
        for (int i = 0; i < sizeof(flagBitPercent)/sizeof(flagBitPercent[0]); i++) {
            if ((double)rand() / (RAND_MAX) * 100 < flagBitPercent[i] * PROB_FACTOR) {
                flags |= 1 << i;
            }
        }
    }
    return flags;
}

int driver_create_file(const char *path, int flags, int mode, bool is_uniform_flag)
{

    int fd = open(path, flags, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t driver_write_file(const char *path, int flags, void *data, off_t offset, size_t length, bool is_uniform_flag)
{
    int fd = open(path, flags, O_RDWR);
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
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}
