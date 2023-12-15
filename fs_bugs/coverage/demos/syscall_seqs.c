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

#define LOOP_MAX 10

void print_error(char *name) { 
    fprintf(stderr, "%s syscall failed: %s\n", name, strerror(errno)); 
    exit(1);
}

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <fs-type> <mountpoint> [device]\n", argv[0]);
        exit(1);
    }
    char *mp = NULL, *dev = NULL, *fs_type = NULL;
    fs_type = argv[1];
    mp = argv[2];
    if (strcmp("ext4", fs_type) == 0) {
        dev = argv[3];
        // Mount for ext4
        mount_fs(dev, mp, fs_type);
    }

    char test_file[PATH_MAX] = {0};
    char test_dir[PATH_MAX] = {0};

    int loop_id = 0;
    int ret = -1;
    int offset = 0, writelen = 0, writebyte = 0, filelen = 0;
    char *data = NULL;
    while (loop_id < LOOP_MAX) {
        snprintf(test_file, PATH_MAX, "%s/test-%d.txt", mp, loop_id);
        snprintf(test_dir, PATH_MAX, "%s/testdir-%d", mp, loop_id); 
        // create_file
        ret = create_file(test_file, O_CREAT|O_WRONLY|O_TRUNC, 0644);
        if (ret < 0) {
            print_error("create_file");
        }

        // write_file
        offset = loop_id / 2;
        writelen = loop_id;
        writebyte = loop_id;
        data = malloc(writelen);
        generate_data(data, writelen, writebyte);
        ret = write_file(test_file, O_RDWR, data, (off_t)offset, (size_t)writelen);
        if (ret < 0) {
            print_error("write_file");
        }
        free(data);

        // truncate
        if (loop_id % 2 == 0)
            filelen = loop_id / 2;
        else
            filelen = loop_id * 2;
        ret = truncate(test_file, (off_t)filelen);
        if (ret < 0) {
            print_error("truncate");
        }

        // unlink
        ret = unlink(test_file);
        if (ret < 0) {
            print_error("unlink");
        }        

        // mkdir
        ret = mkdir(test_dir, 0755);
        if (ret < 0) {
            print_error("mkdir");
        }

        // rmdir
        ret = rmdir(test_dir);
        if (ret < 0) {
            print_error("rmdir");
        } 
        
        ++loop_id;
    }

    // Unmount
    unmount_fs(mp, fs_type);

    return 0;
}

