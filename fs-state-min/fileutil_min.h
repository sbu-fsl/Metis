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

// #include "setup_min.h"

#ifndef _FILEUTIL_H_
#define _FILEUTIL_H_

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

// #ifndef _SETUP_H_
// #define _SETUP_H_

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

// #define DRIVER_ABORT_MINS 40

// #define GCOV_ABORT_MINS 30

#define XATTR_BUF_SIZE 256
static const char *xattr_names[] = {"user.mcfsone", "user.mcfstwo"};
static const char *xattr_vals[] = {"MCFSValueOne", "MCFSValueTwo"};

extern globals_t *globals_t_p;
extern struct fs_stat *fsinfos;
extern int cur_pid;
extern char func[FUNC_NAME_LEN + 1];
extern struct timespec begin_time;
extern struct timespec epoch;
extern int _opened_files[1024];
extern int _n_files;
extern size_t count;
extern char *basepaths[];
extern absfs_set_t absfs_set;
extern int pan_argc;
extern char **pan_argv;
extern int absfs_hash_method;
extern bool enable_fdpool;
extern bool enable_complex_ops;

#ifdef CBUF_IMAGE
extern circular_buf_sum_t *fsimg_bufs;
#endif

struct fs_stat {
    size_t capacity;
    size_t bytes_free;
    size_t bytes_avail;
    size_t total_inodes;
    size_t free_inodes;
    size_t block_size;
};

struct imghash {
    unsigned char md5[16];
    size_t count;
};

static inline void get_epoch()
{
    struct timespec now;
    current_utc_time(&now);
    timediff(&epoch, &now, &begin_time);
}

static inline void makelog(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    get_epoch();
    submit_message("[%4ld.%09ld] ", epoch.tv_sec, epoch.tv_nsec);
    vsubmit_message(format, args);
}

static inline void record_seq(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    vsubmit_seq(format, args);
}

static inline void compute_abstract_state(const char *basepath,
    absfs_state_t state)
{
    absfs_t absfs;

    absfs.hash_option = absfs_hash_method;
    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, false, submit_error);
    memcpy(state, absfs.state, sizeof(absfs_state_t));
    destroy_abstract_fs(&absfs);
}

#define makecall(retvar, err, argfmt, funcname, ...) \
    count++; \
    memset(func, 0, FUNC_NAME_LEN + 1); \
    strncpy(func, #funcname, FUNC_NAME_LEN); \
    cur_pid = Pworker->_pid; \
    record_seq("%s, " argfmt "\n", func, __VA_ARGS__); \
    errno = 0; \
    retvar = funcname(__VA_ARGS__); \
    err = errno; \
    makelog("[seqid = %zu] %s (" argfmt ")", \
            count, func, __VA_ARGS__); \
    submit_message(" -> ret = %d, err = %s\n", retvar, strerror(errno)); \
    errno = err;

#define logwarn(msg, ...) \
    get_epoch(); \
    submit_error("[%4ld.%09ld] %s:%d:%s: " msg "\n", epoch.tv_sec, \
                 epoch.tv_nsec, __FILE__, __LINE__, __func__, ##__VA_ARGS__);

#define logerr(msg, ...) \
    get_epoch(); \
    submit_error("[%4ld.%09ld] %s:%d:%s: " msg " (%s)\n", epoch.tv_sec, \
                 epoch.tv_nsec, __FILE__, __LINE__, __func__, ##__VA_ARGS__, \
                 strerror(errno));

#define min(x, y) ((x >= y) ? y : x)

static inline void print_expect_failed(const char *expr, const char *file,
                                       int line)
{
    logerr("[seqid=%zu] Expectation failed at %s:%d: %s\n",
           count, file, line, expr);
}

#ifdef CBUF_IMAGE
static inline void dump_all_cbufs()
{
    dump_all_circular_bufs(fsimg_bufs, get_fslist(), get_devsize_kb());
}
#endif

#ifndef ABORT_ON_FAIL
#define ABORT_ON_FAIL 0
#endif

#ifdef CBUF_IMAGE
#define expect(expr) \
    do { \
        if (!(expr)) { \
            print_expect_failed(#expr, __FILE__, __LINE__); \
            dump_all_cbufs(); \
            if (ABORT_ON_FAIL) { \
                fflush(stderr); \
                exit(1); \
            } \
        } \
    } while(0)
#else
#define expect(expr) \
    do { \
        if (!(expr)) { \
            print_expect_failed(#expr, __FILE__, __LINE__); \
            if (ABORT_ON_FAIL) { \
                fflush(stderr); \
                exit(1); \
            } \
        } \
    } while(0)
#endif

/* Randomly pick a value in the range of [min, max] */
static inline size_t pick_value(size_t min, size_t max, size_t step)
{
    return min + rand() / (RAND_MAX / (max - min + 1) + 1) / step * step;
}

enum fill_type {PATTERN, ONES, BYTE_REPEAT, RANDOM_EACH_BYTE};

/* Randomly pick a value in the range of [min, max] without steps */
static inline size_t pick_random(size_t min, size_t max)
{
   return min + rand() / (RAND_MAX / (max - min + 1) + 1);
}

/* Generate data into a given buffer.
 * @value: 0-255 for uniform characters, -1 for random filling */
static inline void generate_data(char *buffer, size_t len, size_t offset, enum fill_type type, int value)
{
    switch (type) {
    /* ONES: write all byte 1 */
    case ONES:
        memset(buffer, 1, len);
        break;
    /* BYTE_REPEAT: select a random byte but write this byte uniformly */
    case BYTE_REPEAT:
        memset(buffer, value, len);
        break;
    /* PATTERN: write the bytes that are the same as the value of offsets */
    case PATTERN:
    {
        int new_offset = 3 - offset % sizeof(int);
        for (int i = 0; i < new_offset; i++) {
            buffer[i] = 0;
        }
        int *ip = (int *) (buffer + new_offset);
        for (int i = 0; i <= len / sizeof(int); i++) {
            ip[i] = offset / sizeof(int) + i;
        }
        break;
    }
    /* RANDOM_EACH_BYTE: write random value for each int size (4 bytes) */
    case RANDOM_EACH_BYTE:
    {
        size_t i = 0, remaining = len;
        int n = rand();
        while (remaining > 0) {
            int *ptr = (int *)(buffer + i);
            *ptr = n;
            remaining -= min(sizeof(int), remaining);
            i += min(sizeof(int), remaining);
        }
        break;
    }
    }
}

static inline bool check_file_existence(const char *path)
{
    return access(path, F_OK) == 0;
}

static inline ssize_t fsize(int fd)
{
    struct stat info;
    int ret = fstat(fd, &info);
    if (ret != 0)
        return -1;
    if (info.st_mode & S_IFREG) {
        // verify st_size is even multiple of 4096
        const size_t bs = 4096;
        if (info.st_size % bs != 0)
            return -1;
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return -1;
        return devsz;
    } else {
        return -1;
    }
}

bool compare_equality_values(char **fses, int n_fs, int *nums);
bool compare_equality_fexists(char **fses, int n_fs, char **fpaths);
bool compare_equality_fcontent(char **fses, int n_fs, char **fpaths);
bool compare_equality_absfs(char **fses, int n_fs, absfs_state_t *absfs);
bool compare_equality_file_xattr(char **fses, int n_fs, char **xfpaths);
int compare_file_content(const char *path1, const char *path2);

void show_open_flags(uint64_t flags);
int myopen(const char *pathname, int flags, mode_t mode);
void fsimg_checkpoint(const char *mntpoint);
void closeall();
void cleanup();
void mountall();
void unmount_all(bool strict);
void record_fs_stat();
void start_perf_metrics_thread();
bool do_fsck();
int fsfreeze(const char *fstype, const char *devpath, const char *mountpoint);
int fsthaw(const char *fstype, const char *devpath, const char *mountpoint);
int unfreeze_all();
void clear_excluded_files();
// int setup_generic(const char *fsname, const char *devname, const size_t size_kb);
// int setup_jffs2(const char *devname, const size_t size_kb);
// void execute_cmd(const char *cmd);
// int execute_cmd_status(const char *cmd);
// void populate_mountpoints();

static inline void unmount_all_strict()
{
    unmount_all(true);
}

static inline void unmount_all_relaxed()
{
    unmount_all(false);
}

#endif
