#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

int create_file(const char *path, int flags, int mode);
ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length);
int fallocate_file(const char *path, off_t offset, off_t len);

#endif // _OPERATIONS_H
