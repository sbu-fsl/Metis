#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

int create_file(const char *path, int mode);
ssize_t write_file(const char *path, void *data, off_t offset, size_t length);

int nfs_create_file(const char *path, int mode);
int nfs_write_file(const char *path, void *data, off_t offset, size_t length);
int nfs_trunc_file(const char* path);
int nfs_unlink_file(const char* path);
int nfs_create_dir(const char* path);
int nfs_remove_dir(const char* path);

#endif // _OPERATIONS_H
