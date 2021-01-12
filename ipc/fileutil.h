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
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <openssl/md5.h>

#include "nanotiming.h"
// #include "operations.h"
#include "errnoname.h"
#include "vector.h"
#include "abstract_fs.h"
#include "config.h"

#ifndef _FILEUTIL_H_
#define _FILEUTIL_H_

extern int cur_pid;
extern char func[FUNC_NAME_LEN + 1];
extern struct timespec begin_time;
extern int _opened_files[1024];
extern int _n_files;
extern size_t count;
extern char *basepaths[];

struct imghash {
    unsigned char md5[16];
    size_t count;
};

static inline int makelog(const char *format, ...)
{
    struct timespec now, diff;
    va_list args;
    va_start(args, format);
    current_utc_time(&now);
    timediff(&diff, &now, &begin_time);
    printf("[%4ld.%09ld] ", diff.tv_sec, diff.tv_nsec);
    int res = vprintf(format, args);
    fflush(stdout);
    return res;
}

static inline int record_seq(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    int ret = vfprintf(seqfp, format, args);
    fflush(seqfp);
    return ret;
}

static inline void compute_abstract_state(const char *basepath,
    absfs_state_t state)
{
    absfs_t absfs;

    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, false, NULL);
    memcpy(state, absfs.state, sizeof(absfs_state_t));
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
    printf(" -> ret = %d, err = %s\n", retvar, errnoname(errno)); \
    errno = err;

#define min(x, y) ((x >= y) ? y : x)

static inline void print_expect_failed(const char *expr, const char *file,
                                       int line)
{
    fprintf(stderr, "[seqid=%zu] Expectation failed at %s:%d: %s\n",
            count, file, line, expr);
}

#ifndef ABORT_ON_FAIL
#define ABORT_ON_FAIL 0
#endif
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

/* Randomly pick a value in the range of [min, max] */
static inline size_t pick_value(size_t min, size_t max, size_t step)
{
    return min + rand() / (RAND_MAX / (max - min + 1) + 1) / step * step;
}

/* Generate data into a given buffer.
 * @value: 0-255 for uniform characters, -1 for random filling */
static inline void generate_data(char *buffer, size_t len, int value)
{
    if (value > 0) {
        memset(buffer, value, len);
    } else {
        size_t i = 0, remaining = len;
        int n = rand();
        while (remaining > 0) {
            int *ptr = (int *)(buffer + i);
            *ptr = n;
            remaining -= min(sizeof(int), remaining);
            i += min(sizeof(int), remaining);
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
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return 0;
        return devsz;
    } else {
        return 0;
    }
}

bool compare_equality_values(const char **fses, int n_fs, int *nums);
bool compare_equality_fexists(const char **fses, int n_fs, char **fpaths);
bool compare_equality_fcontent(const char **fses, int n_fs, char **fpaths);
bool compare_equality_absfs(const char **fses, int n_fs, absfs_state_t *absfs);
int compare_file_content(const char *path1, const char *path2);

void show_open_flags(uint64_t flags);
int myopen(const char *pathname, int flags, mode_t mode);
void fsimg_checkpoint(const char *mntpoint);
void closeall();
void cleanup();
void mountall();
void unmount_all();
void record_fs_stat();
void start_perf_metrics_thread();
bool do_fsck();
int fsfreeze(const char *fstype, const char *devpath, const char *mountpoint);
int fsthaw(const char *fstype, const char *devpath, const char *mountpoint);
int unfreeze_all();
void clear_excluded_files();

#endif