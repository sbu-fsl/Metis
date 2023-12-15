/*
 * Copyright (c) 2020-2023 Yifei Liu
 * Copyright (c) 2020-2023 Wei Su
 * Copyright (c) 2020-2023 Erez Zadok
 * Copyright (c) 2020-2023 Stony Brook University
 * Copyright (c) 2020-2023 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */
 
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <linux/fs.h>
#include <unistd.h>
#include <fcntl.h>
#include <stddef.h>
#include <malloc.h>

#include "custom_heap.h"

static char *custom_heap_path;
static ssize_t custom_heap_size;
static const char *custom_heap_path_key = "CUSTOM_HEAP_PATH";
static void *myheap_base;
static int myheap_fd = -1;

/* Get the size of a file or block device */
static inline ssize_t fsize(const char *fpath)
{
    struct stat info;
    int fd = open(fpath, O_RDONLY);
    assert(fd >= 0);
    ssize_t ret = fstat(fd, &info);
    if (ret != 0) {
        fprintf(stderr, "%s: cannot fstat '%s' (%d)\n",
                __func__, fpath, errno);
        goto end;
    }
    if (info.st_mode & __S_IFREG) {
        ret = info.st_size;
        goto end;
    } else if (info.st_mode & __S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret != 0) {
            fprintf(stderr, "%s: cannot get the size of block device "
                    "%s (%d).\n", __func__, fpath, errno);
            goto end;
        }
        ret = devsz;
        goto end;
    } else {
        ret = 0;
    }
end:
    close(fd);
    return ret;
}

static int get_params_from_env(void)
{
    custom_heap_path = getenv(custom_heap_path_key);

    /* Validate existence of environment vars */
    if (!custom_heap_path) {
        fprintf(stderr, "%s is not set.\n", custom_heap_path_key);
        return -EINVAL;
    }

    /* The file must be accessible */
    if (access(custom_heap_path, R_OK | W_OK) != 0) {
        fprintf(stderr, "File '%s' is not accessible.\n", custom_heap_path);
        return -ENOENT;
    }

    /* Obtain the size of file */
    custom_heap_size = fsize(custom_heap_path);
    if (custom_heap_size == 0) {
        fprintf(stderr, "File '%s' must be a non-empty regular file or"
                "block device.", custom_heap_path);
        return -EINVAL;
    } else if (custom_heap_size < 0) {
        fprintf(stderr, "Cannot get the size of file '%s'.\n",
                custom_heap_path);
        return -EINVAL;
    }

    return 0;
}

/* Map the custom heap file into address space.
 * get_params_from_env() must be called first to get parameters */
static int setup_myheap(void)
{
    myheap_fd = open(custom_heap_path, O_RDWR);
    assert(myheap_fd >= 0);

    myheap_base = mmap(NULL, custom_heap_size, PROT_READ | PROT_WRITE,
            MAP_SHARED, myheap_fd, 0);
    if (myheap_base == MAP_FAILED) {
        return -errno;
    }
    return 0;
}

void try_init_myheap(void)
{
    int ret = get_params_from_env();
    if (ret != 0) {
        fprintf(stderr, "%s: env is not set properly.\n", __func__);
        return;
    }
    ret = setup_myheap();
    if (ret != 0) {
        fprintf(stderr, "%s: custom heap cannot be initialized (%d).\n",
                __func__, ret);
        return;
    }

    // __morecore = my_morecore;
}

void unset_myheap(void)
{
    if (myheap_base != NULL)
        munmap(myheap_base, custom_heap_size);
    if (myheap_fd >= 0)
        close(myheap_fd);
}

void *my_morecore(ptrdiff_t increment)
{
    static void *current = NULL;
    void *result;

    if (current == NULL) {
        if (myheap_base == NULL) {
            fprintf(stderr, "%s: please set up the custom heap first.\n",
                    __func__);
            abort();
        }
        current = myheap_base;
    }

    if (current + increment > myheap_base + custom_heap_size) {
        return NULL;
    }
    result = current;
    current += increment;
    return result;
}
