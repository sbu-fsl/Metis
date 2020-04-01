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

static inline int compare_file_content(int fd1, int fd2)
{
    const size_t bs = 4096;
    char buf1[bs], buf2[bs];
    struct stat f1, f2;
    int ret = 0;
    /* Get file properties: Make sure equal file size */
    ret = fstat(fd1, &f1);
    if (ret) {
        printf("[%d] cmp_file_content: fstat f1 failed (%d)\n",
               cur_pid, errno);
        return -1;
    }
    ret = fstat(fd2, &f2);
    if (ret) {
        printf("[%d] cmp_file_content: fstat f2 failed (%d)\n",
               cur_pid, errno);
        return -1;
    }
    if (f1.st_size != f2.st_size) {
        printf("[%d] cmp_file_content: f1 and f2 size differ. "
               "f1 has %zu bytes and f2 has %zu.\n", cur_pid,
               f1.st_size, f2.st_size);
        return 1;
    }
    /* Compare the file content */
    int r1, r2;
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
            printf("[%d] cmp_file_content: f1 and f2 content is not equal.\n",
                   cur_pid);
            return 1;
        }
    }
    if (r1 < 0 || r2 < 0) {
        printf("[%d] cmp_file_content: error occurred when reading: %d\n",
               cur_pid, errno);
    }
    return 0;
}

#endif
