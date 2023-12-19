/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include "mounts.h"

void mount_fs(char *dev_name, char *mp_path, char *fs_type)
{
    int ret = -1; 
    int err = 0;
    errno = 0;
    ret = mount(dev_name, mp_path, fs_type, MS_NOATIME, "");
    if (ret != 0) {
        err = errno;
        goto err;
    }
    return;
err:
    umount2(mp_path, MNT_FORCE);
    fprintf(stderr, "Cannot mount file system %s on %s with mount point %s (%s)\n",
            fs_type, dev_name, mp_path, strerror(err));
    exit(1);
}

void unmount_fs(char *mp_path, char *fs_type)
{
    bool has_failure = false;
    int retry_limit = 20;
    int ret = -1;
    int err = 0;
try_unmount:
    errno = 0;
    ret = umount2(mp_path, 0);
    err = errno;
    if (ret != 0) {
        useconds_t waitms = (100 << (10 - retry_limit));
        if (err == EBUSY && retry_limit > 0) {
            fprintf(stderr, "File system %s mounted on %s is busy. Retry "
                        "unmounting after %dms.\n", fs_type, mp_path, waitms);
            usleep(1000 * waitms);
            retry_limit--;
            goto try_unmount;
        }
        fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                fs_type, mp_path, strerror(err));
        has_failure = true;
    }
    if (has_failure)
        exit(1);
}
