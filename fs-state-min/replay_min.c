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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ftw.h>
#include <assert.h>
#include <stdint.h>
#include <stdarg.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/ioctl.h>
#include <sys/xattr.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <openssl/md5.h>

#include "vector.h"
#include "operations.h"
#include "abstract_fs.h"
#include "nanotiming.h"
// #include "fileutil_min.h" // includes "abstract_fs.h"

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

int pre = 0;
int seq = 0;

void extract_fields(vector_t *fields_vec, char *line, const char *delim)
{
	vector_init(fields_vec, char *);
	char *field = strtok(line, delim);
	while (field) {
		size_t flen = strlen(field);
		char *field_copy = malloc(flen + 1);
		assert(field_copy);
		field_copy[flen] = '\0';
		strncpy(field_copy, field, flen);
		vector_add(fields_vec, &field_copy);
		field = strtok(NULL, ", ");
	}
}

void destroy_fields(vector_t *fields_vec)
{
	char **field;
	vector_iter(fields_vec, char *, field) {
		free(*field);
	}
	vector_destroy(fields_vec);
}

int do_create_file(vector_t *argvec)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *flagstr = *vector_get(argvec, char *, 2);
	char *modestr = *vector_get(argvec, char *, 3);
	char *endptr;
	int flags = (int)strtol(flagstr, &endptr, 8);
	int mode = (int)strtol(modestr, &endptr, 8);
	int res = create_file(filepath, flags, mode);
	printf("create_file(%s, 0%o, 0%o) -> ret=%d, errno=%s\n",
	       filepath, flags, mode, res, strerror(errno));
	return res;
}

int do_write_file(vector_t *argvec, int seq)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *flagstr = *vector_get(argvec, char *, 2);
	char *offset_str = *vector_get(argvec, char *, 4);
	char *len_str = *vector_get(argvec, char *, 5);
	char *endp;
	int flags = (int)strtol(flagstr, &endp, 8);
	off_t offset = strtol(offset_str, &endp, 10);
	size_t writelen = strtoul(len_str, &endp, 10);
	assert(offset != LONG_MAX);
	assert(writelen != ULONG_MAX);
	
	char *buffer = malloc(writelen);
	assert(buffer != NULL);
	/* This is to make sure data written to all file systems in the same
	 * group of operations is the same */
	int integer_to_write = seq / get_n_fs();
	generate_data(buffer, writelen, offset, BYTE_REPEAT, integer_to_write);
	int ret = write_file(filepath, flags, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %o, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, flags, offset, writelen, ret, strerror(err));
	free(buffer);
	return ret;
}

int do_unlink(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = unlink(path);
	int err = errno;
	printf("unlink(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
	return ret;
}

int do_mkdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	char *modestr = *vector_get(argvec, char *, 2);
	char *endp;
	int mode = (int)strtol(modestr, &endp, 8);
	int ret = mkdir(path, mode);
	int err = errno;
	printf("mkdir(%s, 0%o) -> ret=%d, errno=%s\n",
	       path, mode, ret, strerror(err));
	return ret;
}

int do_rmdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = rmdir(path);
	int err = errno;
	printf("rmdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
	return ret;
}

void populate_replay_basepaths()
{
	for (int i = 0; i < get_n_fs(); ++i) {
		size_t len = snprintf(NULL, 0, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
		get_basepaths()[i] = calloc(1, len + 1);
		snprintf(get_basepaths()[i], len + 1, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
	}
}

char *get_replayed_absfs(const char *basepath,
    unsigned int hash_method, char *abs_state_str)
{
    int ret;
    absfs_t absfs;
    absfs.hash_option = hash_method;
    init_abstract_fs(&absfs);
    ret = scan_abstract_fs(&absfs, basepath, false, printf);

    if (ret) {
        printf("Error occurred when computing absfs...\n");
        return NULL;
    }

    char *strp = abs_state_str;
    for (int i = 0; i < 16; ++i) {
        size_t res = snprintf(strp, 3, "%02x", absfs.state[i]);
        strp += res;
    }
    destroy_abstract_fs(&absfs);
    return abs_state_str;
}

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


static void execute_cmd(const char *cmd)
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

int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

static int check_device(const char *devname, const size_t exp_size_kb)
{
    int fd = open(devname, O_RDONLY);
    struct stat devinfo;
    if (fd < 0) {
        fprintf(stderr, "Cannot open %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        return -errno;
    }
    int retval = fstat(fd, &devinfo);
    if (retval < 0) {
        fprintf(stderr, "Cannot stat %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        close(fd);
        return -errno;
    }
    if (!S_ISBLK(devinfo.st_mode)) {
        fprintf(stderr, "%s is not a block device.\n", devname);
        close(fd);
        return -ENOTBLK;
    }
    size_t devsize = fsize(fd);
    if (devsize < exp_size_kb * 1024) {
        fprintf(stderr, "%s is smaller than expected (expected %zu KB, "
                "got %zu).\n", devname, exp_size_kb, devsize / 1024);
        close(fd);
        return -ENOSPC;
    }
    close(fd);
    return 0; 
}

static void populate_mountpoints()
{
    char check_mount_cmdbuf[PATH_MAX];
    char unmount_cmdbuf[PATH_MAX];
    char check_mp_exist_cmdbuf[PATH_MAX];
    char rm_mp_cmdbuf[PATH_MAX];
    char mk_mp_cmdbuf[PATH_MAX];
    for (int i = 0; i < get_n_fs(); ++i) {
        snprintf(check_mount_cmdbuf, PATH_MAX, "mount | grep %s", get_basepaths()[i]);    
        /* If the mountpoint has fs mounted, then unmount it */
        if (execute_cmd_status(check_mount_cmdbuf) == 0) {
            snprintf(unmount_cmdbuf, PATH_MAX, "umount -f %s", get_basepaths()[i]);
            execute_cmd(unmount_cmdbuf);
        }
        /* 
         * Caveat: if we use file/dir pools and test in-memory file systems
         * like VeriFS, we should not remove the mount point here because
         * we need to pre-create files/dirs in the pool. Removing mountpoints
         * simply erase the precreated files/dirs.
         *
         * Also, we cannot mount VeriFS and other in-memory file systems on
         * a non-empty mount point.
         * 
         * The correct way would be removing and recreating mount point of 
         * VeriFS in the setup shell scripts before running pan.
         */

        snprintf(mk_mp_cmdbuf, PATH_MAX, "mkdir -p %s", get_basepaths()[i]);
        execute_cmd(mk_mp_cmdbuf);
    }
}

static int setup_jfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.jfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

void setup_filesystems()
{
    int ret;
    populate_mountpoints();

    for (int i = 0; i < get_n_fs(); ++i) {
        if (strcmp(get_fslist()[i], "jfs") == 0) {
            ret = setup_jfs(get_devlist()[i], get_devsize_kb()[i]);
        }
    }
    
    if (ret != 0)
    {
        fprintf(stderr, "Cannot setup JFS file system (ret = %d)\n", ret);
        exit(1);
    }
}

int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode)
{
    const size_t len = strlen(path);
    char _path[PATH_MAX];
    char *p; 

    errno = 0;

    /* Copy string so its mutable */
    if (len > sizeof(_path)-1) {
        errno = ENAMETOOLONG;
        return -1; 
    }   
    strcpy(_path, path);

    bool next_f = false;
    bool next_d = false;
    /* Iterate the string */
    for (p = _path + 1; *p; p++) {
        if (*p == '/') {
            /* Temporarily truncate */
            *p = '\0';
            if (mkdir(_path, dir_mode) != 0) {
                if (errno != EEXIST) {
                    return -1; 
                }
            }
            
            *p = '/';

            if (*(p + 1) == 'f')
                next_f = true;
            else if (*(p + 1) == 'd')
                next_d = true;
        }
    }
    if (next_f) {
        int fd = creat(_path, file_mode);
        if (fd >= 0) {
            close(fd);
        }
        else if (errno != EEXIST) {
            return -1;
        }
    }
    if (next_d) {
        if (mkdir(_path, dir_mode) != 0) {
            if (errno != EEXIST) {
                return -1; 
            }
        }
    }

    return 0;
}
/* 
 * NOTE: NEED TO RECOMPILE REPLAYER "make replayer" every time we run it.
 *
 * Make sure the required devices are already set up with correct sizes. 
 *
 * Before running this program, make sure the devices are already set 
 * up with correct sizes.
 * We need to specify a sequence.log file (the sequence of operations 
 * to be replayed)
 * and a dump_prepopulate_*.log file (precreated files and dirs).
 * Usage: 
 *		sudo ./replay -K 0:ext4:256:jfs:16384 2>&1 > replay_jfs.log
 *		sudo ./replay -K 0:ext4:256:nilfs2:1028
 *		sudo ./replay -K 0:nilfs2:1028
 */
int main(int argc, char **argv)
{
	/* 
	 * Open the dump_prepopulate_*.log files to create the pre-populated
	 * files and directories.
	 */
	char *dump_prepopulate_file_name = "dump_prepopulate_0_kh6.log";
    char *sequence_log_file_name = "sequence-pan-20240209-182859-244192_kh6.log";

    FILE *pre_fp = fopen(dump_prepopulate_file_name, "r");
	
	if (!pre_fp) {
		printf("Cannot open %s. Does it exist?\n", dump_prepopulate_file_name);
		exit(1);
	}
	
	/* Open sequence file */
	FILE *seqfp = fopen(sequence_log_file_name, "r");
	
	if (!seqfp) {
		printf("Cannot open %s. Does it exist?\n", sequence_log_file_name);
		exit(1);
	}

	ssize_t len, pre_len;
	size_t linecap = 0, pre_linecap = 0;
	char *linebuf = NULL, *pre_linebuf = NULL;

	/* Populate mount points and mkfs the devices */
	setup_filesystems();
	/* Create the pre-populated files and directories */
	mountall();
	while ((pre_len = getline(&pre_linebuf, &pre_linecap, pre_fp)) >= 0) {
		char *line = malloc(pre_len + 1);
		line[pre_len] = '\0';
		strncpy(line, pre_linebuf, pre_len);
		/* remove the newline character */
		if (line[pre_len - 1] == '\n')
			line[pre_len - 1] = '\0';
		printf("pre=%d \n", pre);
		/* parse the line for pre-populated files and directories */
		size_t pre_path_len;
		char *pre_path_name;
		for (int i = 0; i < get_n_fs(); ++i) {
			pre_path_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], line);
			pre_path_name = calloc(1, pre_path_len + 1);
			snprintf(pre_path_name, pre_path_len + 1, "%s%s", get_basepaths()[i], line);
			// printf("pre_path_name=%s\n", pre_path_name);
			int ret = -1;
			ret = mkdir_p(pre_path_name, 0755, 0644);
			if (ret < 0) {
				fprintf(stderr, "mkdir_p error happened!\n");
				exit(EXIT_FAILURE);
			}
			free(pre_path_name);
		}
		pre++;
	}
	unmount_all_strict();
	/* Replay the actual operation sequence */
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d \n", seq);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);

		mountall();
		
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
			do_write_file(&argvec, seq);
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(&argvec);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(&argvec);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(&argvec);
		} else if (strncmp(funcname, "checkpoint", len) == 0 || strncmp(funcname, "restore", len) == 0) {
			seq--;
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		
		seq++;

		unmount_all_strict();
		errno = 0;
		free(line);
		destroy_fields(&argvec);
	}
	/* Clean up */
	fclose(pre_fp);
	fclose(seqfp);
	free(pre_linebuf);
	free(linebuf);

	return 0;
}
