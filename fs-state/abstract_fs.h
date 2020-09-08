#ifndef _ABSTRACT_FS_H
#define _ABSTRACT_FS_H

#include "vector.h"
#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <limits.h>
#include <unistd.h>
#include <openssl/md5.h>

#ifndef PATH_MAX
#define PATH_MAX    4096
#endif

struct absfs_file {
    char *fullpath;
    struct {
        mode_t mode;
        size_t size;
        nlink_t nlink;
        uid_t uid;
        gid_t gid;
    } attrs;
    uint64_t datahash; // Hash value of the file content
};

static inline void init_abstract_fs(vector_t *absfs)
{
    vector_init(absfs, struct absfs_file);
}

int scan_abstract_fs(const char *basepath, vector_t *vec);
uint64_t get_abstract_fs_hash(vector_t *absfs);
void destroy_abstract_fs(vector_t *absfs);

#endif // _ABSTRACT_FS_H
