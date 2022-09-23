#include <sys/types.h>

#ifndef _OPERATIONS_H
#define _OPERATIONS_H

int create_file(const char *path, int mode);
int create_file_excl(const char *path, int mode);
ssize_t write_file(const char *path, void *data, off_t offset, size_t length);

#endif // _OPERATIONS_H
