#include <stdio.h>
#include <stdlib.h>
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

#include "vector.h"

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
#define CRM_FILE_ATTR(filep)  (filep)->entry_param.attr
#define CRM_FILE_MODE(filep)  (filep)->entry_param.attr.st_mode
#define CRM_FILE_SIZE(filep)  (filep)->entry_param.attr.st_size
#define CRM_DEFAULT_ICAP      10
#define CRM_INIT_DIR_CAP      8

struct crmfs_state {
  size_t nfiles;
  struct crmfs_file *files;
};

#endif // _CRMFS_H_
