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

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/xattr.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <openssl/md5.h>

#include "nanotiming.h"
#include "operations.h"
// #include "errnoname.h"
#include "vector.h"
#include "abstract_fs.h"
// #include "set_min.h"
// #include "log.h"
#include "init_globals_min.h"
#ifdef CBUF_IMAGE
// #include "circular_buf.h"
#define CBUF_SIZE 10
#define KB_TO_BYTES 1024

struct fsimg_buf {
    void *state; // concrete state (f/s image buffer)
    bool ckpt; // if true, checkpointed image; if false, restored image
    size_t depth; // state_depth
    size_t seqid; // seq id (count) corresponds to the image
};

typedef struct fsimg_buf fsimg_buf_t;

// Circular buffer structure for each file system
struct circular_buf {
    fsimg_buf_t img_buf[CBUF_SIZE];
    size_t head_idx; // [0, CBUF_SIZE - 1]
    size_t size; // The size of currently saved images, size <= CBUF_SIZE
};

typedef struct circular_buf circular_buf_t;

// Data structure to represent all the circular buffers in MCFS
// The number of circular buffer is equivalent to the number of file systems
struct circular_buf_sum {
    circular_buf_t *cir_bufs; // length is number of f/s 
    unsigned int buf_num; // number of file systems
};

typedef struct circular_buf_sum circular_buf_sum_t;

void circular_buf_init(circular_buf_sum_t **fsimg_bufs, int n_fs, size_t *devsize_kb);
void insert_circular_buf(circular_buf_sum_t *fsimg_bufs, int fs_idx, 
                            size_t devsize_kb, void *save_state, 
                            size_t state_depth, size_t seq_id, bool is_ckpt);
void dump_all_circular_bufs(circular_buf_sum_t *fsimg_bufs, char **fslist, 
    size_t *devsize_kb);
void cleanup_cir_bufs(circular_buf_sum_t *fsimg_bufs);

#endif

#ifndef _SETUP_H_
#define _SETUP_H_

#define VERIFS_PREFIX       "veri"
#define NOVA_NAME           "nova"
#define BTRFS_NAME          "btrfs"
#define XFS_NAME            "xfs"
#define VERIFS1_NAME        "verifs1"
#define NILFS2_NAME         "nilfs2"
#define TESTFS_NAME       "testFS"
#define VERIFS_PREFIX_LEN   (sizeof(VERIFS_PREFIX) - 1)

#ifdef __cplusplus
extern "C" {
#endif

// From set_min.h
typedef struct AbsfsSet* absfs_set_t;

void absfs_set_init(absfs_set_t *set);
void absfs_set_destroy(absfs_set_t set);
int absfs_set_add(absfs_set_t set, absfs_state_t *states);
size_t absfs_set_size(absfs_set_t set);

// From log.h
struct logger {
    FILE *file;
    /* name: relative or absolute path to the log file, but excludes
     * the '.log' extension suffix. */
    char *name;
    size_t bytes_written;
    /* To be assigned from stat.st_mode */
    mode_t type;
};

struct log_entry {
    struct logger *dest;
    size_t loglen;
    char *content;
};

// Get a string of current date and time in the format of yyyymmdd-hhmmss
static inline void get_datetime_stamp(char *strbuf, size_t maxlen) {
  time_t now;
  struct tm now_tm;
  now = time(NULL);
  gmtime_r(&now, &now_tm);
  strftime(strbuf, maxlen, "%Y%m%d-%H%M%S", &now_tm);
}

static inline void add_ts_to_logname(char *strbuf, size_t maxlen,
    const char *logname, const char *progname, const char *suffix) {
  // yyyymmdd-hhmmss'\0' -> total 16 characters
  char tsbuf[16] = {0};
  get_datetime_stamp(tsbuf, 16);
  snprintf(strbuf, maxlen, "%s-%s-%s-%d%s", logname, progname, tsbuf, getpid(),
           suffix);
}

int submit_log(struct logger *dest, const char *fmt, ...);
int submit_message(const char *fmt, ...);
int vsubmit_message(const char *fmt, va_list args);
int submit_error(const char *fmt, ...);
int vsubmit_error(const char *fmt, va_list args);
int submit_seq(const char *fmt, ...);
int vsubmit_seq(const char *fmt, va_list args);
void make_logger(struct logger *lgr, const char *name, FILE *default_fp);
void init_log_daemon(const char *output_log_name, const char *err_log_name,
        const char *seq_name);
void destroy_log_daemon();
ssize_t get_progname(char *outbuf);

#ifdef __cplusplus
}
#endif

void setup_filesystems();
int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode);

int execute_cmd_status(const char *cmd);

#endif // _SETUP_H_

