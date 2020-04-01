#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <linux/limits.h>
#include <unistd.h>

#ifndef _FILEUTIL_H_
#define _FILEUTIL_H_

/* State variables */
int cur_pid;
char func[9];

#define makecall(retvar, err, argfmt, funcname, ...) \
    memset(func, 0, 9); \
    strncpy(func, #funcname, 9); \
    cur_pid = Pworker->_pid; \
    retvar = funcname(__VA_ARGS__); \
    err = errno; \
    printf("[%d] %s (" argfmt ")", cur_pid, func, __VA_ARGS__); \
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

int compare_file_content(int fd1, int fd2);

#endif
