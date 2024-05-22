/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include "config_min.h"
// #include "abstract_fs.h"

#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <limits.h>
#include <unistd.h>
#include <openssl/opensslv.h>
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
#include <openssl/evp.h>
#else
#include <openssl/md5.h>
#endif
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

#ifdef __cplusplus
extern "C" {
#endif

//From abstract_fs.h
#include <xxhash.h>
#include <zlib.h>

    typedef unsigned char absfs_state_t[16];
    typedef int (*printer_t)(const char *fmt, ...);

    enum hash_type{xxh128_t, xxh3_t, md5_t,crc32_t};

    struct abstract_fs {
        unsigned int hash_option;
        union{
            XXH3_state_t *xxh_state;
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
            EVP_MD_CTX *md5_state;
#else
            MD5_CTX md5_state;
#endif
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

#ifndef MAX_FS
#define MAX_FS      20
#endif

#define ENV_KEY_MAX 20

#ifndef MAX_DIR_NUM
#define MAX_DIR_NUM 200
#endif

#define nelem(array)  (sizeof(array) / sizeof(array[0]))

#define mem_alloc_err(...) \
    do { \
        fprintf(stderr, "memory allocation failed: %s:%d:%s\n", \
            __FILE__, __LINE__, __func__, ##__VA_ARGS__); \
        exit(EXIT_FAILURE); \
    } while(0)

typedef struct all_dev_nums {
    int all_rams;
    int all_mtdblocks;
    int all_pmems;
//   int all_loops;
} dev_nums_t;

static const char *fs_all[] = {"btrfs", "ext2", "ext4", "f2fs", 
                               "jffs2", "ramfs", "tmpfs", "verifs1", 
                               "verifs2", "xfs", "nilfs2", "jfs",
                               "nova", "testFS"};
                               
static const char *dev_all[]= {"ram", "ram", "ram", "ram", 
                                "mtdblock", "", "", "", 
                                "", "ram", "ram", "ram",
                                "pmem", "ram"};
#define ALL_FS nelem(fs_all)

static inline int get_dev_from_fs(char *fs_type) {
    int ret = -1;
    for (int i = 0; i < ALL_FS; ++i) {
        if (strcmp(fs_type, fs_all[i]) == 0) 
            return i;
    }
    return ret;
}

#ifdef FILEDIR_POOL
static inline bool is_prefix(const char *pre, const char *str)
{
    if (strlen(pre) > strlen(str))
        return false;
    return strncmp(pre, str, strlen(pre)) == 0;
}
#endif

typedef struct all_global_params {
    int _swarm_id;
    unsigned int _n_fs;
    char **fslist;
    char **fssuffix;
    char **devlist;
    size_t *devsize_kb;
    char **basepaths;
    char **testdirs;
    char **testfiles;
    void **fsimgs;
    int *fsfds;
    absfs_state_t *absfs;
    int *rets;
    int *errs;
    /* Fields related to new operations and dir structure */
    int fpoolsize;
    int dpoolsize;
    char ***filepool; // number of file systems -> size of file pool -> each file pathname
    char ***directorypool;
    /* Fields on xattr */
    char **xfpaths;
} globals_t;

extern globals_t *globals_t_p;
extern bool *fs_frozen;

static inline unsigned int get_n_fs() {
    return globals_t_p->_n_fs;
}

static inline char **get_fslist() {
    return globals_t_p->fslist;
}

static inline char **get_fssuffix() {
    return globals_t_p->fssuffix;
}

static inline char **get_devlist() {
    return globals_t_p->devlist;
}

static inline size_t *get_devsize_kb() {
    return globals_t_p->devsize_kb;
}

static inline char **get_basepaths() {
    return globals_t_p->basepaths;
}

static inline char **get_testdirs() {
    return globals_t_p->testdirs;
}

static inline char **get_testfiles() {
    return globals_t_p->testfiles;
}

static inline void **get_fsimgs() {
    return globals_t_p->fsimgs;
}

static inline int *get_fsfds() {
    return globals_t_p->fsfds;
}

static inline absfs_state_t *get_absfs() {
    return globals_t_p->absfs;
}

static inline int *get_rets() {
    return globals_t_p->rets;
}

static inline int *get_errs() {
    return globals_t_p->errs;
}

static inline int get_fpoolsize() {
    return globals_t_p->fpoolsize;
}

static inline int get_dpoolsize() {
    return globals_t_p->dpoolsize;
}

static inline char ***get_filepool() {
    return globals_t_p->filepool;
}

static inline char ***get_directorypool() {
    return globals_t_p->directorypool;
}

static inline char **get_xfpaths() {
    return globals_t_p->xfpaths;
}

#ifdef FILEDIR_POOL
extern char **bfs_fd_pool;
extern int combo_pool_idx;
#endif

#ifdef __cplusplus
}
#endif

//From abstract_fs.h
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

/* End of C++ declarations */

#endif // _INIT_GLOBALS_H_

