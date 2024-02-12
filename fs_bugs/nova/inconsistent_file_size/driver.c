/*
 * File:   driver.c
 * Author: Stony Brook University FSL
 * Date:   February 9, 2024
 * Brief:  This file reproduces kernel hang in NOVA fs by repeatedly mounting-unmounting it in a tight loop.
 * 
 * Copyright (c) [year] [author]
 * 
 */

#include <stdio.h>
#include <stdlib.h>
#include <sys/mount.h>
#include <sys/wait.h>
#include <limits.h>

int execute_cmd_status(const char *cmd)
{
    if (cmd == NULL) {
    fprintf(stderr, "Command should not be NULL.\n");
    return -1;
    }
       
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

int main(int argc, char **argv)
{
    char *nova_mp = NULL;
    char *nova_dev = NULL;
    long loop_max;
    char cmdbuf[PATH_MAX];
    int ret = -1;
    long loop_id = 0;

    if (argc < 3)
    {
        fprintf(stderr, "Usage: %s <nova-mountpoint> <nova-device> <loop-max>\n",
                argv[0]);
        exit(1);
    }

    nova_mp = argv[1];
    nova_dev = argv[2];
    loop_max = atol(argv[3]);

    // Mount and initialise NOVA for the first time. This is similar to mkfs
    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA -o init %s %s", nova_dev, nova_mp);
    ret = execute_cmd_status(cmdbuf);

    if (ret != 0)
    {
        fprintf(stderr, "Failed to init mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
        exit(1);
    }

    ret = umount2(nova_mp, 0);
    if (ret != 0)
    {
        fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
        exit(1);
    }

    // Now that the file system has been initialized, mounted, and unmounted, we will proceed with the mount-unmount loop.
    while (loop_id < loop_max)
    {
        fprintf(stdout, "loop_id: %ld\n", loop_id);

        // Mount NOVA
        snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", nova_dev, nova_mp);
        ret = execute_cmd_status(cmdbuf);

        if (ret != 0)
        {
            fprintf(stderr, "Failed to mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
            exit(1);
        }

        // Unmount NOVA
        ret = umount2(nova_mp, 0);
        if (ret != 0)
        {
            fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
            exit(1);
        }

        ++loop_id;
    }

    fprintf(stdout, "No discrepancy found, EXITING\n");
    return 0;
}
