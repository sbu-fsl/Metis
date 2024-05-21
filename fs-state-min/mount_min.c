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

#define _XOPEN_SOURCE 500
#define _POSIX_C_SOURCE 2
#include "fileutil_min.h"

void mountall()
{
    int failpos, err;
    for (int i = 0; i < get_n_fs(); ++i) {
        int ret = -1;
        ret = mount(get_devlist()[i], get_basepaths()[i], get_fslist()[i], MS_NOATIME, "");     
        if (ret != 0) {
            failpos = i;
            err = errno;
            goto err;
        }
    }
    return;
err:
    /* undo mounts */
    for (int i = 0; i < failpos; ++i) {
        umount2(get_basepaths()[i], MNT_FORCE);
    }
    fprintf(stderr, "Could not mount file system %s in %s at %s (%s)\n",
            get_fslist()[failpos], get_devlist()[failpos], get_basepaths()[failpos],
            strerror(err));
    exit(1);
}

static void save_lsof()
{
    int ret;
    static int report_count = 0;
    char progname[NAME_MAX] = {0};
    char logname[NAME_MAX] = {0};
    char cmd[PATH_MAX] = {0};

    get_progname(progname);
    add_ts_to_logname(logname, NAME_MAX, "lsof", progname, "");
    ret = snprintf(cmd, PATH_MAX, "lsof > %s-%d.txt", logname, report_count++);
    assert(ret >= 0);
    ret = system(cmd);
}

void unmount_all(bool strict)
{
    bool has_failure = false;
    int ret;
#ifndef NO_FS_STAT
    record_fs_stat();
#endif
    for (int i = 0; i < get_n_fs(); ++i) {
        // Change retry limit from 20 to 19 to avoid excessive delay
        int retry_limit = 19;
        int num_retries = 0;
        /* We have to unfreeze the frozen file system before unmounting it.
         * Otherwise the system will hang! */
        /*
        if (fs_frozen[i]) {
            fsthaw(get_fslist()[i], get_devlist()[i], get_basepaths()[i]);
        }
        */
    
        while (retry_limit > 0) {
            ret = umount2(get_basepaths()[i], 0);
            if (ret == 0) {
                break; // Success, exit the retry loop
            }        

            /* If unmounting failed due to device being busy, again up to
            * retry_limit times with 100 * 2^n ms (n = num_retries) */
            if (errno == EBUSY) {
                // 100 * (1 <<  0) = 100ms
                // 100 * (1 << 18) = 100 * 262144 = 26.2144s
                useconds_t waitms = 100 * (1 << num_retries); // Exponential backoff starting at 100ms
                fprintf(stderr, "File system %s mounted on %s is busy. Retry %d times,"
                        "unmounting after %dms.\n", get_fslist()[i], get_basepaths()[i], num_retries + 1,
                        waitms);
                usleep(1000 * waitms);
                num_retries++;
                retry_limit--;
                save_lsof();
            } 
            else {
                // Handle non-EBUSY errors immediately without retrying
                fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                        get_fslist()[i], get_basepaths()[i], strerror(errno));
                has_failure = true;
            }
        }
        
        if (retry_limit == 0) {
            fprintf(stderr, "Failed to unmount file system %s at %s after retries.\n",
                    get_fslist()[i], get_basepaths()[i]);
            has_failure = true;
        }
    }
    if (has_failure && strict)
        exit(1);
}