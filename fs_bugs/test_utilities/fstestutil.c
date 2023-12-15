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

#include "fstestutil.h"

int randSyscall(int ops_num, char *test_file, char *test_dir)
{
    int ret = -1;
    int offset = 0, writelen = 0, writebyte = 0, filelen = 0;
    switch(ops_num) {
        case 0:
            ret = create_file(test_file, O_CREAT|O_WRONLY|O_TRUNC, 0644);
            break;
        case 1:
            offset = getRandNum(0, 65536);
            writelen = getRandNum(0, 64409);
            writebyte = getRandNum(1, 255);
            char *data = malloc(writelen);
            generate_test_data(data, writelen, writebyte);
            ret = write_file(test_file, O_RDWR, data, (off_t)offset, (size_t)writelen);
            free(data);
            break;
        case 2:
            filelen = getRandNum(0, 262144);
            ret = truncate(test_file, (off_t)filelen);
            break;
        case 3:
            ret = unlink(test_file);
            break;
        case 4:
            ret = mkdir(test_dir, 0755);
            break;
        case 5:
            ret = rmdir(test_dir);
            break;
        default:
            fprintf(stderr, "Unrecognized ops_num: %d\n", ops_num);
            exit(-1);
    }
    return ret;
}

int randSyscallChanger(int ops_num, char *test_file, char *test_dir, bool *changed)
{
    int ret = -1;
    int offset = 0, writelen = 0, writebyte = 0, filelen = 0;
    *changed = false;
    switch(ops_num) {
        case 0:
            ret = create_file(test_file, O_CREAT|O_WRONLY|O_EXCL, 0644);
            if (ret == 0)
                *changed = true;
            break;
        case 1:
            offset = getRandNum(0, 65536);
            writelen = getRandNum(0, 64409);
            writebyte = getRandNum(1, 255);
            char *data = malloc(writelen);
            generate_test_data(data, writelen, writebyte);
            ret = write_file(test_file, O_RDWR, data, (off_t)offset, (size_t)writelen);
            free(data);
            if (ret > 0)
                *changed = true;
            break;
        case 2:
            filelen = getRandNum(0, 262144);
            ret = truncate(test_file, (off_t)filelen);
            if (ret == 0)
                *changed = true;
            break;
        case 3:
            ret = unlink(test_file);
            if (ret == 0)
                *changed = true;
            break;
        case 4:
            ret = mkdir(test_dir, 0755);
            if (ret == 0)
                *changed = true;
            break;
        case 5:
            ret = rmdir(test_dir);
            if (ret == 0)
                *changed = true;
            break;
        default:
            fprintf(stderr, "Unrecognized ops_num: %d\n", ops_num);
            exit(-1);
    }
    return ret;
}

void execute_cmd(const char *cmd)
{
    int retval = system(cmd);
    int status, signal = 0;
    if ((status = WEXITSTATUS(retval)) != 0) {
        fprintf(stderr, "Command `%s` failed with %d.\n", cmd, status);
    }
    if (WIFSIGNALED(retval)) {
        signal = WTERMSIG(retval);
        fprintf(stderr, "Command `%s` terminated with signal %d.\n", cmd,
                signal);
    }
    if (status || signal) {
        exit(1);
    }
}

void file_CRC32(char *file_path, crc32_state_t *crc32_hash)
{
    int fd = open(file_path, O_RDONLY);
    if (fd < 0) {
        fprintf(stderr, "Open failed for CRC32.\n");
        exit(1);
    }

    char buffer[BUF_SIZE] = {0};
    ssize_t readsize = 0;
    int ret = -1;
    uLong crc32_state;
    while ((readsize = read(fd, buffer, BUF_SIZE)) > 0) {
        ret = (int)
            (crc32_state = crc32((uLong) crc32_state, (const Bytef *) buffer, 
                            (uInt) readsize));

        memset(buffer, 0, sizeof(buffer));
    }

    if (readsize < 0) {
        fprintf(stderr, "CRC32 Read Error: %s (ret = %d)\n", 
            strerror(errno), ret);
        exit(1);
    }
    close(fd);
    memcpy(crc32_hash, &crc32_state, sizeof(crc32_state_t));
}

