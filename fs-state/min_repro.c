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

/*
 * MCFS minimal bug reproducer 
 */
#include "replayutil.h"

#define MAX_LINE_LENGTH 256

#define MAX_LOOP 1000000

// By default it is 2 for MD5 
unsigned int hash_method = 2;

static long find_last_checkpoint_offset(FILE *seqfp)
{
    int ch, count, i, j;
    long offset = 0;
    bool found_checkpoint = 0;
    char forward_line[MAX_LINE_LENGTH];
    char reverse_line[MAX_LINE_LENGTH];
    // Move file pointer to the end of file
    fseek(seqfp, 0L, SEEK_END);

    // Read file backwards
    while (ftell(seqfp) > 1) {
        fseek(seqfp, -2, SEEK_CUR);
        if (ftell(seqfp) <= 2)
            break;
        // Read one character
        ch = fgetc(seqfp);
        count = 0;
        while(ch != '\n'){
            reverse_line[count] = ch;
            ++count;
            if(ftell(seqfp) < 2)
                break;
            fseek(seqfp, -2, SEEK_CUR);
            ch = fgetc(seqfp);
        }
        // Record current file offset
        offset = ftell(seqfp);
        // Reverse the line 
        j = 0;
        for (i = count - 1; i >= 0 && count > 0; i--) {
            forward_line[j] = reverse_line[i];
            j++;
        }
        forward_line[j] = '\0';
        // Check if the line contains the "checkpoint" string
        if (strstr(forward_line, "checkpoint")) {
            found_checkpoint = 1;
            break;
        }
    }

    if (!found_checkpoint) {
        fprintf(stderr, "No checkpoint found in sequence file\n");
        fclose(seqfp);
        exit(1);
    }

    return offset;
}

int main(int argc, char **argv)
{
    if (argc < 8) {
        fprintf(stderr, "Usage: %s -K fs1:size1:fs2:size2 seqlog img1 img2 dev1 dev2\n", argv[0]);
        exit(1);
    }
    char *seqlog = argv[3];
    char *img1 = argv[4];
    char *img2 = argv[5];
    char *dev1 = argv[6];
    char *dev2 = argv[7];
    FILE *seqfp;
    long offset;
    size_t linecap = 0;
    ssize_t len;
    long loop_num = 0;

    srand(time(NULL));

    // Read sequence file from bottom to top
    seqfp = fopen(seqlog, "r");
    if (seqfp == NULL) {
        fprintf(stderr, "Cannot open sequence.log. Does it exist?\n");
        exit(1);
    }

    offset = find_last_checkpoint_offset(seqfp);
    // printf("Got offset: %ld\n", offset);
    populate_replay_basepaths();

    // Start the loop
    while (loop_num < MAX_LOOP) {
        printf("Loop %ld\n", loop_num);
        char cmdbuf1[PATH_MAX];
        char cmdbuf2[PATH_MAX];
        // Copy from image file to device file via dd
        snprintf(cmdbuf1, PATH_MAX,
                "dd if=%s of=%s bs=1k bs=4k status=none",
                img1, dev1);
        execute_cmd(cmdbuf1);
        snprintf(cmdbuf2, PATH_MAX,
                "dd if=%s of=%s bs=1k bs=4k status=none",
                img2, dev2);
        execute_cmd(cmdbuf2);

        // Seek to offset of last checkpoint
        fseek(seqfp, offset, SEEK_SET);

        int ops_cnt = 0;
        char *linebuf = NULL;
        // Read the file from the offset
        while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
            // Copy the line
            char *line = malloc(len + 1);
            line[len] = '\0';
            strncpy(line, linebuf, len);
            /* remove the newline character */
            if (line[len - 1] == '\n')
                line[len - 1] = '\0';
            /* parse the line */
            vector_t argvec;
            extract_fields(&argvec, line, ", ");
            char *funcname = *vector_get(&argvec, char *, 0);
            // Mount the file systems
            mountall();
            if (strncmp(funcname, "create_file", len) == 0) {
                do_create_file(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "write_file", len) == 0) {
                do_write_file(&argvec, loop_num % 256);
                ++ops_cnt;
            } else if (strncmp(funcname, "truncate", len) == 0) {
                do_truncate(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "unlink", len) == 0) {
                do_unlink(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "mkdir", len) == 0) {
                do_mkdir(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "rmdir", len) == 0) {
                do_rmdir(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "rename", len) == 0) {
                do_rename(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "symlink", len) == 0) {
                do_symlink(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "link", len) == 0) {
                do_link(&argvec);
                ++ops_cnt;
            } else if (strncmp(funcname, "checkpoint", len) != 0 && 
                    strncmp(funcname, "restore", len) != 0) {
                printf("Unrecognized op: %s\n", funcname);
                exit(1);
            }
            // Calculate and compare abstract state for two file systems
            if (ops_cnt == get_n_fs()) {
                char *absfs_str1 = calloc(ABSFS_STR_LEN, sizeof(char));
                char *absfs_str2 = calloc(ABSFS_STR_LEN, sizeof(char));

                char *absfs_ret1 = get_replayed_absfs(get_basepaths()[0], hash_method, absfs_str1);
                char *absfs_ret2 = get_replayed_absfs(get_basepaths()[1], hash_method, absfs_str2);

                if (strncmp(absfs_ret1, absfs_ret2, ABSFS_STR_LEN) != 0) {
                    printf("Abstract state mismatch!\n");
                    printf("Abstract state for %s: %s\n", get_basepaths()[0], absfs_ret1);
                    printf("Abstract state for %s: %s\n", get_basepaths()[1], absfs_ret2);
                    exit(1);
                }
                free(absfs_str1);
                free(absfs_str2);

                ops_cnt = 0;
            }
            // Unmount the file systems
            unmount_all_strict();
            free(line);
            destroy_fields(&argvec);
        }
        if (linebuf) {
            free(linebuf);
        }
        loop_num++;
    }
    // Close the file
    fclose(seqfp);

    return 0;
}
