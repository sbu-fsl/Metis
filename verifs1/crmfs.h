#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>
#include <unistd.h>
#include <fcntl.h>
#include <linux/limits.h>
#include <sys/types.h>
#include <pthread.h>

#include "cr.h"

#if !defined(FUSE_USE_VERSION) || FUSE_USE_VERSION < 30
#define FUSE_USE_VERSION 30
#endif
#define _FILE_OFFSET_BITS 64

#ifdef __APPLE__
#include <osxfuse/fuse/fuse_lowlevel.h>
#else
#include <fuse/fuse_lowlevel.h>
#endif

#ifndef _CRMFS_H_
#define _CRMFS_H_

struct crmfs_file {
  uint32_t flag;
  int32_t nlookup;
  struct fuse_entry_param entry_param;
  void *data;
};

struct crmfs_dirent {
  fuse_ino_t ino;
  char name[NAME_MAX];
};

struct crmfs_dirtable {
  size_t capacity;
  size_t ndirs;
  struct crmfs_dirent dirents[0];
};

#define CRM_BLOCK_SZ          512
#define CRM_FILE_EXIST        1
#define CRM_FILE_ATTR(filep, key)  (filep)->entry_param.attr.st_##key
#define CRM_FILE_MODE(filep)  (filep)->entry_param.attr.st_mode
#define CRM_FILE_SIZE(filep)  (filep)->entry_param.attr.st_size
#define CRM_DEFAULT_ICAP      10
#define CRM_INIT_DIR_CAP      8

struct crmfs_state {
  size_t nfiles;
  struct crmfs_file *files;
};

static inline void *ERR_PTR(long error)
{
  return (void *) error;
}

static inline long PTR_ERR(void *ptr)
{
  return (long) ptr;
}

#ifndef MAX_ERRNO
#define MAX_ERRNO   4095
#endif
static inline bool IS_ERR(void *ptr)
{
  return (unsigned long) ptr >= (unsigned long) -MAX_ERRNO;
}

static inline size_t round_up(size_t n, size_t unit)
{
  return ((n + unit - 1) / unit) * unit;
}

static inline size_t round_down(size_t n, size_t unit)
{
  return round_up(n, unit) - unit;
}

static inline size_t nblocks(size_t size)
{
  if (size == 0) {
    return 0;
  } else {
    return round_up(size, CRM_BLOCK_SZ) / CRM_BLOCK_SZ;
  }
}

static inline mode_t get_umask(void)
{
  mode_t mask = umask(0);
  umask(mask);
  return mask;
}

static inline void _crmfs_debug(const char *fmt, ...)
{
#ifdef DEBUG
  va_list args;
  va_start(args, fmt);
  vfprintf(stderr, fmt, args);
  va_end(args);
#endif
}

#define debug(msg, ...) \
  _crmfs_debug("%s: " msg, __func__, ##__VA_ARGS__)

#define enter() _crmfs_debug("%s\n", __func__);

#endif // _CRMFS_H_
