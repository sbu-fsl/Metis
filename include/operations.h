#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

int create_file(const char *path, int mode);
ssize_t write_file(const char *path, void *data, off_t offset, size_t length);
int mv(const char *path1, const char *path2);

#endif // _OPERATIONS_H
