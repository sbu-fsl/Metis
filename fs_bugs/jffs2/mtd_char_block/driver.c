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

#include "mounts.h"
#include "fstestutil.h"

int main(int argc, char *argv[])
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <mountpoint> <loop_max>\n", argv[0]);
        exit(1);
    }
    char *mp = NULL;
    char *char_dev = "mtd0", *blk_dev = "/dev/mtdblock0", *fs_type = "jffs2";

    mp = argv[1];
    const long loop_max = atol(argv[2]);
    long loop_id = 0;
    char cmdbuf[PATH_MAX];
    // Set up test file and directory pathname
    char test_file[PATH_MAX] = {0};
    char test_dir[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/test.txt", mp);
    snprintf(test_dir, PATH_MAX, "%s/testdir", mp);

    bool is_changed = false;
    int ret = -1;
    crc32_state_t curr_hash, prev_hash;
    int ops_num = -1;

    while (loop_id < loop_max) {
        fprintf(stdout, "loop_id: %ld\n", loop_id);
        // Mount jffs2 using mtd char dev
        snprintf(cmdbuf, PATH_MAX, "mount -t jffs2 %s %s", char_dev, mp);
        execute_cmd(cmdbuf);

        file_CRC32(blk_dev, &prev_hash);

        // Do a random operation and check if the state is supposed to change
        ops_num = getRandNum(0, SYSCALL_NUM - 1);
        ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);

        // Compute MTD block hash
        file_CRC32(blk_dev, &curr_hash);

        if (is_changed) {
            fprintf(stdout, "changed\n");
        }
        // Compare to previous one and check if the state change is corresponding to operation
        if (is_changed && memcmp(&curr_hash, &prev_hash, sizeof(crc32_state_t)) == 0) {
            fprintf(stderr, "Error: mtdblock does not reflect mtd char dev\n");
            exit(1);
        }
        
        /*
        if (!is_changed && memcmp(&curr_hash, &prev_hash, sizeof(crc32_state_t)) != 0) {
            fprintf(stderr, "Error: state is not supposed to be changed!\n");
            exit(1);
        }
        */

        // Unmount
        unmount_fs(mp, fs_type);
        ++loop_id;
    }

    return 0;
}
