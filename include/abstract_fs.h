#ifndef _ABSTRACT_FS_H
#define _ABSTRACT_FS_H

#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <limits.h>
#include <unistd.h>
#include <openssl/md5.h>
#include <string.h>
#include <dirent.h>

#ifndef PATH_MAX
#define PATH_MAX    4096
#endif

#define SYSCALL_RETRY_LIMIT 5
#define RETRY_WAIT_USECS    1000
#define with_retry(retry_cond, retry_limit, wait_us, retry_action, retval, \
                   func, ...) \
    int _retry_count = 0; \
    do { \
        retval = func(__VA_ARGS__); \
        if (!(retry_cond)) { \
            break; \
        } else { \
            retry_action(#func, #retry_cond, _retry_count + 1); \
            usleep(wait_us); \
        } \
    } while (_retry_count++ < retry_limit);


/* Function prototypes and definitions for C programs */
#ifdef __cplusplus
extern "C" {
#endif
#include <xxhash.h>
#include <zlib.h>

    typedef unsigned char absfs_state_t[16];
    typedef int (*printer_t)(const char *fmt, ...);

    enum hash_type{xxh128_t, xxh3_t, md5_t,crc32_t};

    struct abstract_fs {
        unsigned int hash_option;
        union{
            XXH3_state_t *xxh_state;
            MD5_CTX md5_state;
            uLong crc32_state;
        };
        absfs_state_t state;
    };

    typedef struct abstract_fs absfs_t;

    void init_abstract_fs(absfs_t *absfs);
    void destroy_abstract_fs(absfs_t *absfs);
    int scan_abstract_fs(absfs_t *absfs, const char *basepath, bool verbose,
                         printer_t verbose_printer);
    void print_abstract_fs_state(printer_t printer, const absfs_state_t state);
    void print_filemode(printer_t printer, mode_t mode);

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
        memcpy(&prefix, &absfs->md5_state, sizeof(uint32_t));
        return prefix;
    }

    static inline size_t round_up(size_t n, size_t unit) {
        return ((n + unit - 1) / unit) * unit;
    }

    static inline size_t round_down(size_t n, size_t unit) {
        return round_up(n, unit) - unit;
    }

#ifdef __cplusplus
}
#endif
/* End of prototypes and definitions for C programs */




/* C++ declarations */
#ifdef __cplusplus

#include <vector>
#include <experimental/filesystem>

namespace fs = std::experimental::filesystem;

typedef int (*printer_t)(const char *fmt, ...);

struct AbstractFile {
    std::string fullpath;
    /* Abstract path is irrelevant to the basepath of the mount point */
    std::string abstract_path;
    struct {
        mode_t mode;
        size_t size;
        nlink_t nlink;
        uid_t uid;
        gid_t gid;
    } attrs;

    struct {
        blksize_t blksize;
        blkcnt_t blocks;
    } _attrs;

    /* Feed the attributes and content of the file described by
     * this AbstractFile into MD5 hash calculator and update the
     * MD5 context object. */
    printer_t printer;

    void FeedHasher(absfs_t *absfs);

    bool CheckValidity();

    /* System call wrappers that can retry on EBUSY */
    int Open(int flag);

    ssize_t Read(int fd, void *buf, size_t count);

    int Lstat(struct stat *statbuf);

    DIR *Opendir();

    struct dirent *Readdir(DIR *dirp);

    int Closedir(DIR *dirp);

private:
    void retry_warning(const std::string& funcname, const std::string& cond, int retry_count) const;
};

#define DEFINE_SYSCALL_WITH_RETRY(ret_type, func, ...) \
    ret_type _ret; \
    with_retry(((intptr_t)_ret < 0 && errno == EBUSY), SYSCALL_RETRY_LIMIT, \
               RETRY_WAIT_USECS, retry_warning, _ret, func, __VA_ARGS__); \
    return _ret;

#endif

#endif // _ABSTRACT_FS_H
/* End of C++ declarations */
