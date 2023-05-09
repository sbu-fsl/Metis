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
#include "errnoname.h"
#include "vector.h"
#include "abstract_fs.h"
#include "set.h"
#include "log.h"
#include "init_globals.h"
#ifdef CBUF_IMAGE
#include "circular_buf.h"
#endif

#ifndef _SETUP_H_
#define _SETUP_H_

#define VERIFS_PREFIX       "veri"
#define NOVA_NAME           "nova"
#define BTRFS_NAME          "btrfs"
#define XFS_NAME            "xfs"
#define VERIFS1_NAME        "verifs1"
#define NILFS2_NAME         "nilfs2"
#define VERIFS_PREFIX_LEN   (sizeof(VERIFS_PREFIX) - 1)

static inline bool is_verifs(const char *fsname)
{
    return strncmp(fsname, VERIFS_PREFIX, VERIFS_PREFIX_LEN) == 0;
}

static inline bool is_nova(const char *fsname)
{
    return strcmp(fsname, NOVA_NAME) == 0;
}

void setup_filesystems();

int execute_cmd_status(const char *cmd);

#endif // _SETUP_H_
