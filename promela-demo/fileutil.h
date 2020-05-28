#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <linux/limits.h>
#include <unistd.h>

#include "nanotiming.h"
#include "operations.h"

#ifndef _FILEUTIL_H_
#define _FILEUTIL_H_

/* State variables */
int cur_pid;
char func[9];
struct timespec begin_time;

int _opened_files[1024];
int _n_files;

static inline int makelog(const char *format, ...)
{
    struct timespec now, diff;
    va_list args;
    va_start(args, format);
    current_utc_time(&now);
    timediff(&diff, &now, &begin_time);
    printf("[%4ld.%09ld] ", diff.tv_sec, diff.tv_nsec);
    return vprintf(format, args);
}

#define makecall(retvar, err, argfmt, funcname, ...) \
    memset(func, 0, 9); \
    strncpy(func, #funcname, 9); \
    cur_pid = Pworker->_pid; \
    errno = 0; \
    retvar = funcname(__VA_ARGS__); \
    err = errno; \
    makelog("[PROC #%d] %s (" argfmt ")", cur_pid, func, __VA_ARGS__); \
    printf(" -> %d\n", retvar);

#define min(x, y) ((x >= y) ? y : x)

/* Randomly pick a value in the range of [min, max] */
static inline size_t pick_value(size_t min, size_t max)
{
    return min + rand() * (max - min) / RAND_MAX;
}

/* Generate data into a given buffer.
 * @value: 0-255 for uniform characters, -1 for random filling */
static inline void generate_data(char *buffer, size_t len, int value)
{
    if (value > 0) {
        memset(buffer, value, len);
    } else {
        size_t i = 0, remaining = len;
        while (remaining > 0) {
            int n = rand();
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

bool compare_equality_values(char **fses, int n_fs, int *nums);
bool compare_equality_fexists(char **fses, int n_fs, char **fpaths);
bool compare_equality_fcontent(char **fses, int n_fs, char **fpaths, int *fds);
int compare_file_content(int fd1, int fd2);

void show_open_flags(uint64_t flags);
int myopen(const char *pathname, int flags, mode_t mode);
void cleanup();

#endif
