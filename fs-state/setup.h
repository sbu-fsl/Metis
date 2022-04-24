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
#include "operations.h"
#include "errnoname.h"
#include "vector.h"
#include "abstract_fs.h"
#include "config.h"
#include "set.h"
#include "log.h"
#include "init_globals.h"

#ifndef _SETUP_H_
#define _SETUP_H_

#define VERIFS_PREFIX       "veri"
#define VERIFS_PREFIX_LEN   (sizeof(VERIFS_PREFIX) - 1)

static inline bool is_verifs(const char *fsname)
{
    return strncmp(fsname, VERIFS_PREFIX, VERIFS_PREFIX_LEN) == 0;
}

void setup_filesystems();

#endif // _SETUP_H_
