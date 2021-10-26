#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>

#include <nfsc/libnfs.h>

int create_file(const char *path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, void *data, off_t offset, size_t length)
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
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

struct nfs_context *nfs = NULL;
struct nfsfh *nfsfh = NULL;

static int init_nfs_context() {
    nfs = nfs_init_context();

    if (nfs == NULL) {
        return errno;
    }

    return 0;
}

int nfs_create_file(const char *path, int mode) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_creat(nfs, path, mode, &nfsfh);
    errno = err;

exit_err:
    return errno;
}

// nfs_write, nfs, nfsfh, testfiles[i], data,
//                          (off_t)Pworker->offset, (size_t)Pworker->writelen);
int nfs_write_file(const char *path, void *data, off_t offset, size_t length) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_write(nfs, nfsfh, length, data);
    errno = err;

exit_err:
    return errno;
}

int nfs_trunc_file(const char* path) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_truncate(nfs, path, 0);
    errno = err;

exit_err:
    return errno;

}

int nfs_unlink_file(const char* path) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_unlink(nfs, path);
    errno = err;

exit_err:
    return errno;
}

int nfs_create_dir(const char* path) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_mkdir(nfs, path);
    errno = err;

exit_err:
    return errno;
}

int nfs_remove_dir(const char* path) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_rmdir(nfs, path);
    errno = err;

exit_err:
    return errno;
}