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
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <sys/vfs.h>

#ifndef _MOUNTS_H
#define _MOUNTS_H

#define min(x, y) ((x >= y) ? y : x)

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

void mount_fs(char *dev_name, char *mp_path, char *fs_type);
void unmount_fs(char *mp_path, char *fs_type);

#endif // _MOUNTS_H


