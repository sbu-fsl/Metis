#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

int create_file(const char *path, int flags, int mode);
ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length);
int fallocate_file(const char *path, off_t offset, off_t len);
int chown_file(const char *path, uid_t owner);
int chgrp_file(const char *path, gid_t group);

#endif // _OPERATIONS_H
