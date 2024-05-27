/*
 * File:   driver.c
 * Date:   February 9, 2024
 * Brief:  This file reproduces kernel hang in NOVA fs by repeatedly mounting-unmounting it in a tight loop.
 * 
 * Copyright (c) 2020-2024 Gautam Ahuja
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include <stdio.h>
#include <stdlib.h>
#include <sys/mount.h>
#include <sys/wait.h>
#include <limits.h>
#include <unistd.h>

int execute_cmd_status(const char *cmd)
{
    if (cmd == NULL) 
    {
        fprintf(stderr, "Command should not be NULL.\n");
        return -1;
    }

    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

int main(int argc, char **argv)
{

    long loop_max = 1;
    char cmdbuf[PATH_MAX];
    int ret = -5;
    long loop_id = 0;



    while (loop_id < loop_max)
    {

    ret = mount("/dev/ram1", "/mnt/server", "ext4", MS_NOATIME, NULL);
    // snprintf(cmdbuf, PATH_MAX, "mount -t ext4 /dev/ram1 /mnt/server");
    //  ret = execute_cmd_status(cmdbuf);
    fprintf(stderr, "EXT4 mount, ret=%d\n", ret);

    snprintf(cmdbuf, PATH_MAX, "exportfs -o rw,sync,no_root_squash localhost:/mnt/server");
    ret = execute_cmd_status(cmdbuf);
    fprintf(stderr, "Executed command = %s, ret=%d\n", cmdbuf, ret);

    ret = mount("localhost:/mnt/server", "/mnt/local", "nfs", MS_NOATIME, "rw,sync,vers=3,addr=127.0.0.1");
    fprintf(stderr, "NFS mount, ret=%d\n", ret);

    ret = umount2("/mnt/local", 0);
     fprintf(stderr, "NFS unmount, ret=%d\n", ret);


    snprintf(cmdbuf, PATH_MAX, "exportfs -u localhost:/mnt/server");
    ret = execute_cmd_status(cmdbuf);
    fprintf(stderr, "Executed command = %s, ret=%d\n", cmdbuf, ret);
    
    usleep(5000000);
    // snprintf(cmdbuf, PATH_MAX, "umount /dev/ram1");
    // ret = execute_cmd_status(cmdbuf);
    ret = umount2("dev/ram1", 0);
    fprintf(stderr, "EXT4 unmount, ret=%d\n", ret);
    ++loop_id;
    }
    return 0;
}
