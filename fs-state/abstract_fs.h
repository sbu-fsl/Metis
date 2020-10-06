#ifndef _ABSTRACT_FS_H
#define _ABSTRACT_FS_H

#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <limits.h>
#include <unistd.h>
#include <openssl/md5.h>
#include <string.h>

#ifndef PATH_MAX
#define PATH_MAX    4096
#endif

/* C++ declarations */
#ifdef __cplusplus

#include <vector>
#include <experimental/filesystem>

namespace fs = std::experimental::filesystem;

struct AbstractFile {
    fs::path fullpath;
    /* Abstract path is irrelevant to the basepath of the mount point */
    fs::path abstract_path;
    struct {
        mode_t mode;
        size_t size;
        nlink_t nlink;
        uid_t uid;
        gid_t gid;
    } attrs;

    /* Feed the attributes and content of the file described by
     * this AbstractFile into MD5 hash calculator and update the
     * MD5 context object. */
    void FeedHasher(MD5_CTX *ctx);
};

#endif
/* End of C++ declarations */

/* Function prototypes and definitions for C programs */
#ifdef __cplusplus
extern "C" {
#endif

struct abstract_fs {
  MD5_CTX ctx;
  unsigned char state[16];
};

typedef struct abstract_fs absfs_t;

void init_abstract_fs(absfs_t *absfs);
int scan_abstract_fs(absfs_t *absfs, const char *basepath);
void print_abstract_fs_state(absfs_t *absfs);

/**
 * get_state_prefix: Get the 32-bit prefix of the "abstract file
 *   system state signature", which is a 128-bit MD5 hash
 *
 * @param[in] absfs: The abstract file system object
 *
 * @return: First 32-bit of the state hash value
 */
static inline uint32_t get_state_prefix(absfs_t *absfs) {
  uint32_t prefix;
  memcpy(&prefix, absfs->state, sizeof(uint32_t));
  return prefix;
}

#ifdef __cplusplus
}
#endif
/* End of prototypes and definitions for C programs */

#endif // _ABSTRACT_FS_H
