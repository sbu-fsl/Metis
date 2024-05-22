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

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include "config_min.h"
// #include "init_globals_min.h"

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

// extern globals_t *globals_t_p;
// extern bool *fs_frozen;

globals_t *globals_t_p;
bool *fs_frozen;
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
// globals_t *globals_t_p;
// bool *fs_frozen;
#ifdef FILEDIR_POOL
char **bfs_fd_pool;
int combo_pool_idx;
#endif

static char *mcfs_globals_env;
static const char *mcfs_globals_env_key = "MCFS_FSLIST";
static const char *globals_delim = ":";
static const char *ramdisk_name = "ram";
static const char *mtdblock_name = "mtdblock";
static const char *pmem_name = "pmem";
//static const char *loop_name = "loop";

static char *fslist_to_copy[MAX_FS];
static size_t devsize_kb_to_copy[MAX_FS];
static char *global_args = NULL;
static int opt_ret = -1;

#ifdef FILEDIR_POOL
static int fpool_idx = 0;
static int dpool_idx = 0;

/* Temp file and dir pools are freed in precreate_pools */
static char **tmp_fpool = NULL;
static char **tmp_dpool = NULL;
#endif

dev_nums_t dev_nums = {.all_rams = 0, .all_mtdblocks = 0, .all_pmems=0};

/*
 * current is the list of directories previous depth
 * size is current's size.
 */
#ifdef FILEDIR_POOL
static void pool_dfs(int path_depth, char** current, int size) {
    int newnames_len = 0;
    /* newpool: directories at the current depth. */
    char *newpool[MAX_DIR_NUM];
    int append = 0;
    /* 
     * Iterate through directories in the previous depth(stored in current)
     * append each d-[j] to each current[i] and add to directorypool
     * also add this to the newpool
     */
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < DIR_COUNT; j++) {
            /* -2 is for length of "d-" */
            append = MCFS_NAME_LEN - 2;
            size_t len = snprintf(NULL, 0, "%s/d-%0*d", 
                current[i], append, j);
            newpool[newnames_len] = calloc(1, 1 + len);
            snprintf(newpool[newnames_len], 1 + len, "%s/d-%0*d", 
                current[i], append, j);

            tmp_dpool[dpool_idx] = calloc(1, 1 + len);
            snprintf(tmp_dpool[dpool_idx], 1 + len, "%s/d-%0*d", 
                current[i], append, j);
            dpool_idx++;
            newnames_len++;
        }
    }
    /* 
     * Iterate through directories in the previous depth(stored in current)
     * append "f-j" to current[i] and add to filepool
     */
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < FILE_COUNT; j++) {
            /* -2 is for "f-" */
            append = MCFS_NAME_LEN - 2;
            size_t len = snprintf(NULL, 0, "%s/f-%0*d", 
                current[i], append, j);

            tmp_fpool[fpool_idx] = calloc(1, 1+len);
            snprintf(tmp_fpool[fpool_idx], 1+len, "%s/f-%0*d", 
                current[i], append, j);
            fpool_idx++;
        }
        free(current[i]);
    }
    if (path_depth == 1) {
        return;
    }

    pool_dfs(path_depth - 1, newpool, newnames_len);
}

static int getpowsum(int dircnt, int path_depth) {
    int sum = 0;
    int current = 1;
    for(int i = 0; i < path_depth; i++){
        current *= dircnt;
        sum += current;
    }
    return sum;
}
#endif

static void init_globals_pointer()
{
    /* global structure pointer */
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p)
        mem_alloc_err();
    /* set default erroneous swarm id */
    globals_t_p->_swarm_id = -1;
}

static int parse_cli_arguments(char* args_to_parse)
{
    /* Parsing the MCFS options from env */
    int tok_cnt = -1;
    char *context = NULL;
    bool first_tok = true;
    /* Example: ext4:256:jffs2:512 fs1:size1(KB):fs2:size2(KB) */
    char *token = strtok_r(args_to_parse, globals_delim, &context);
    while (token != NULL) {
        /* First token for CLI option is Swarm ID */
        if (first_tok) {
            globals_t_p->_swarm_id = atoi(token);
            first_tok = false;
        }
        /* Fetch file system name */
        else if (tok_cnt % 2 == 0) {
            fslist_to_copy[tok_cnt / 2] = calloc(strlen(token) + 1, 
                sizeof(char));
            if (!fslist_to_copy[tok_cnt / 2])
                mem_alloc_err();
            strcpy(fslist_to_copy[tok_cnt / 2], token);
        }
        /* Fetch device size */
        else {
            devsize_kb_to_copy[tok_cnt / 2] = atoi(token);
        }
        ++tok_cnt;
        token = strtok_r(NULL, globals_delim, &context);
    }
    if (tok_cnt % 2 != 0) {
        fprintf(stderr, "Incorrect args format! Eg: 0:fs1:size1:fs2:size2\n");
        return -EINVAL; 
    }
    /* _n_fs */
    globals_t_p->_n_fs = tok_cnt / 2;
    return 0;
}

static int get_mcfs_cli_arguments()
{
    int ret = -1;
    ret = parse_cli_arguments(global_args);
    return ret;
}

/* swarm_id should already be gotten before this function */
static int parse_env_arguments(char* env_to_parse)
{
    /* Parsing the MCFS options from env */
    int tok_cnt = 0;
    char *context = NULL;
    /* Example: ext4:256:jffs2:512 fs1:size1(KB):fs2:size2(KB) */
    char *token = strtok_r(env_to_parse, globals_delim, &context);
    while (token != NULL) {
        /* Fetch file system name */
        if (tok_cnt % 2 == 0) {
            fslist_to_copy[tok_cnt / 2] = calloc(strlen(token) + 1, 
                sizeof(char));
            if (!fslist_to_copy[tok_cnt / 2])
                mem_alloc_err();
            strcpy(fslist_to_copy[tok_cnt / 2], token);
        }
        /* Fetch device size */
        else {
            devsize_kb_to_copy[tok_cnt / 2] = atoi(token);
        }
        ++tok_cnt;
        token = strtok_r(NULL, globals_delim, &context);
    }
    if (tok_cnt % 2 != 0) {
        fprintf(stderr, "Incorrect env format! Exp: fs1:size1:fs2:size2\n");
        return -EINVAL; 
    }
    /* _n_fs */
    globals_t_p->_n_fs = tok_cnt / 2;
    return 0;
}

static int get_mcfs_env_arguments() 
{
    char globals_used_env_key[ENV_KEY_MAX];
    /* 
     * No swarm mode (single Spin pan process), Use swarm id 0 
     * Swarm mode, Use swarm id starting from 1
     */
    globals_t_p->_swarm_id = atoi(global_args);
    /* USE MCFS_FSLIST${_swarm_id} as env name */
    sprintf(globals_used_env_key, "%s%u", mcfs_globals_env_key, 
        globals_t_p->_swarm_id);

    mcfs_globals_env = getenv(globals_used_env_key);
    /* Validate existence of environment vars */
    if (!mcfs_globals_env) {
        fprintf(stderr, "globals env %s is not set.\n", 
            globals_used_env_key);
        return -EINVAL;
    }
    int ret = -1;
    ret = parse_env_arguments(mcfs_globals_env);
    return ret;
}

static void prepare_dev_suffix()
{
    /* figure out total number of ram/mtdblocks gonna be used */
    int dev_idx = -1;
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        dev_idx = get_dev_from_fs(fslist_to_copy[i]);
        if (dev_idx == -1) {
	    fprintf(stderr, "Inside first for-loop of prepare_dev_suffix() in init_globals.c");
            fprintf(stderr, "File system type not supported for device\n");
            exit(EXIT_FAILURE);
        }
        else if (strcmp(dev_all[dev_idx], ramdisk_name) == 0) {
            ++dev_nums.all_rams;
        }
        else if (strcmp(dev_all[dev_idx], mtdblock_name) == 0) {
            ++dev_nums.all_mtdblocks;
        }else if (strcmp(dev_all[dev_idx], pmem_name) == 0) {
            ++dev_nums.all_pmems;
        } 
	//else if (strcmp(dev_all[dev_idx], loop_name) == 0) {
        //    ++dev_nums.all_loops;
        //}
    }
    dev_idx = -1;

    /* populate device name (including orginal and used dev names) */
    size_t len;
    int ram_cnt = 0, mtdblock_cnt = 0, pmem_cnt=0;
    int ram_id = -1, mtdblock_id = -1, pmem_id=0;

    globals_t_p->devlist = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->devlist) 
        mem_alloc_err();
    globals_t_p->fssuffix = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->fssuffix) 
        mem_alloc_err();
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        dev_idx = get_dev_from_fs(fslist_to_copy[i]);
        if (dev_idx == -1) {
	    fprintf(stderr, "Inside second loop of prepare_dev_suffixI() in init_globals.c");
            fprintf(stderr, "File system type not supported\n");
            exit(EXIT_FAILURE);
        }
        else if (strcmp(dev_all[dev_idx], ramdisk_name) == 0) {
            if (globals_t_p->_swarm_id >= 1)
                ram_id = ram_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_rams;
            else 
                ram_id = ram_cnt;
            len = snprintf(NULL, 0, "/dev/%s%d", ramdisk_name, ram_id);
            globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
            snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", 
                ramdisk_name, ram_id);
            ++ram_cnt;
        }
        else if (strcmp(dev_all[dev_idx], mtdblock_name) == 0) {
            if (globals_t_p->_swarm_id >= 1)
                mtdblock_id = mtdblock_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_mtdblocks;
            else
                mtdblock_id = mtdblock_cnt;
            len = snprintf(NULL, 0, "/dev/%s%d", mtdblock_name, mtdblock_id);
            globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
            snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", 
                mtdblock_name, mtdblock_id);
            ++mtdblock_cnt;
        }
        else if (strcmp(dev_all[dev_idx], pmem_name) == 0) {
            if (globals_t_p->_swarm_id >= 1)
                pmem_id = pmem_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_pmems;
            else
                pmem_id = pmem_cnt;
            len = snprintf(NULL, 0, "/dev/%s%d", pmem_name, pmem_id);
            globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
            snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", 
                pmem_name, pmem_id);
            ++pmem_cnt;
        } 
        //else if (strcmp(dev_all[dev_idx], loop_name) == 0) {
        //    if (globals_t_p->_swarm_id >= 1)
        //       loop_id = loop_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_loops;
        //    else
        //        loop_id = loop_cnt;
        //    len = snprintf(NULL, 0, "/dev/%s%d", loop_name, loop_id);
        //    globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
        //    snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", 
        //        loop_name, loop_id);
        //   ++loop_cnt;
        //}
        else { // No Disk required 
           globals_t_p->devlist[i] = NULL;
        }
        /* Populate fs suffix -- format -$fsid-$swarmid */
        len = snprintf(NULL, 0, "-i%d-s%d", i, globals_t_p->_swarm_id);
        globals_t_p->fssuffix[i] = calloc(len + 1, sizeof(char));
        snprintf(globals_t_p->fssuffix[i], len + 1, "-i%d-s%d", 
            i, globals_t_p->_swarm_id);
    }
}

static void init_all_fickle_globals() 
{
    /* fslist */
    globals_t_p->fslist = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->fslist) 
        mem_alloc_err();
    /* copy each string to fslist */
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->fslist[i] = calloc(strlen(fslist_to_copy[i]) + 1, sizeof(char));
        if (!globals_t_p->fslist[i])
            mem_alloc_err();     
        memcpy(globals_t_p->fslist[i], fslist_to_copy[i], 
            strlen(fslist_to_copy[i]) + 1);
        free(fslist_to_copy[i]);
    }

    /* devsize_kb */
    globals_t_p->devsize_kb = calloc(globals_t_p->_n_fs, sizeof(size_t));
    if (!globals_t_p->devsize_kb)
        mem_alloc_err(); 
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        memcpy(globals_t_p->devsize_kb, devsize_kb_to_copy, 
            sizeof(size_t) * (globals_t_p->_n_fs));
    }
}

static void init_all_steady_globals() 
{
    /* basepaths */
    globals_t_p->basepaths = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->basepaths) 
        mem_alloc_err();

#ifndef FILEDIR_POOL
    /* testdirs */
    globals_t_p->testdirs = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testdirs) 
        mem_alloc_err();

    /* testfiles */
    globals_t_p->testfiles = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testfiles) 
        mem_alloc_err();
#endif

    /* fsimgs */
    globals_t_p->fsimgs = calloc(globals_t_p->_n_fs, sizeof(void*));
    if (!globals_t_p->fsimgs) 
        mem_alloc_err();

    /* fsfds */
    globals_t_p->fsfds = calloc(globals_t_p->_n_fs, sizeof(int));
    if (!globals_t_p->fsfds) 
        mem_alloc_err();

    /* absfs */
    globals_t_p->absfs = calloc(globals_t_p->_n_fs, sizeof(absfs_state_t));
    if (!globals_t_p->absfs) 
        mem_alloc_err();

    /* rets */
    globals_t_p->rets = calloc(globals_t_p->_n_fs, sizeof(int));
    if (!globals_t_p->rets) 
        mem_alloc_err();

    /* errs */
    globals_t_p->errs = calloc(globals_t_p->_n_fs, sizeof(int));
    if (!globals_t_p->errs) 
        mem_alloc_err();

    /* get_xfpaths */
    globals_t_p->xfpaths = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->xfpaths) 
        mem_alloc_err();
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->xfpaths[i] = NULL;
    }
}

static void init_basepaths()
{
    /* Initialize base paths */
    printf("%d file systems to test.\n", get_n_fs());
    for (int i = 0; i < get_n_fs(); ++i) {
        size_t len = snprintf(NULL, 0, "/mnt/test-%s%s",
                              get_fslist()[i], get_fssuffix()[i]);
        get_basepaths()[i] = calloc(1, len + 1);
        snprintf(get_basepaths()[i], len + 1, "/mnt/test-%s%s",
                 get_fslist()[i], get_fssuffix()[i]);
    }
}

#ifdef FILEDIR_POOL
static void init_multi_files_params()
{
    char *current[PATH_MAX];
    int dpool_sz = 0;
    int fpool_sz = 0;
    if (DIR_COUNT > 0) {
        /*
         * Directory pool size  = no. of dirs at depth 0 + no. of dirs at depth 1 + .....
         * = dircnt + (no. of dirs at depth 0)*dircnt + (no. of dirs at depth 1)*dircnt + ...
         * = dircnt + dircnt*dircnt + dircnt*dircnt*dircnt + .....
         *
         * Similarly, file pool size = no. of files at depth 0 + no. of files at depth 1 + ....
         * = filecnt + (no. of dirs at depth 0)*filecnt + (no. of dirs at depth 1)*filecnt + ...
         * = filecnt * ( 1 + (no. of dirs at depth 0) + (no. of dirs at depth 1) + ....) 
         * = filecnt * (dpool_sz / dircnt);
         */
        dpool_sz = getpowsum(DIR_COUNT, PATH_DEPTH);
        fpool_sz = FILE_COUNT * (dpool_sz / DIR_COUNT);
    }
    else {
        fpool_sz = FILE_COUNT;
    }

    if (dpool_sz > MAX_DIR_NUM || fpool_sz > MAX_DIR_NUM) {
        fprintf(stderr, "Error: configured too many files or directories\nMaximum size: %d\n", 
            MAX_DIR_NUM);
        fprintf(stderr, "fpool_sz value: %d\n", fpool_sz);
        fprintf(stderr, "dpool_sz value: %d\n", dpool_sz);
        exit(1);
    }

    fprintf(stdout, "MCFS: the file pool size: %d\n", fpool_sz);
    fprintf(stdout, "MCFS: the directory pool size: %d\n", dpool_sz);
    fflush(stdout);

    /* Set File and Dir Pool Sizes */
    globals_t_p->fpoolsize = fpool_sz;
    globals_t_p->dpoolsize = dpool_sz;

    /* Allocate temp file and dir pools */
    tmp_fpool = calloc(fpool_sz, sizeof(char*));
    tmp_dpool = calloc(dpool_sz, sizeof(char*));

    /* Initialize filepool */
    globals_t_p->filepool = calloc(globals_t_p->_n_fs, sizeof(char*));

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->filepool[i] = calloc(fpool_sz, sizeof(char*));
    }

    /* Initialize directorypool */
    globals_t_p->directorypool = calloc(globals_t_p->_n_fs, sizeof(char*));

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->directorypool[i] = calloc(dpool_sz, sizeof(char*));
    }

    size_t len = 0;
    current[0] = calloc(1, len + 1);

    if (PATH_DEPTH > 0) {
        pool_dfs(PATH_DEPTH, current, 1);
    }

    /* Populate the file/dir pool in globals */
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        for (int j = 0; j < fpool_sz; ++j) {
            size_t fname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], 
                                        tmp_fpool[j]);
            globals_t_p->filepool[i][j] = calloc(1, fname_len + 1);
            snprintf(globals_t_p->filepool[i][j], fname_len + 1, "%s%s", 
                    get_basepaths()[i], tmp_fpool[j]);
        }

        for (int j = 0; j < dpool_sz; ++j) {
            size_t dname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], 
                                        tmp_dpool[j]);
            globals_t_p->directorypool[i][j] = calloc(1, dname_len + 1);
            snprintf(globals_t_p->directorypool[i][j], dname_len + 1, "%s%s", 
                    get_basepaths()[i], tmp_dpool[j]);       
        }
    }
}

/* 
 * BFS the file and directory pools to pre-create some files & dirs to 
 * reduce ENOENT, need to revisit if this function is really needed
 * bfs_fd_pool free'd at precreate_pools() function
 */
void build_bfs_fdcombo_pool() 
{
    bfs_fd_pool = calloc(get_fpoolsize() + get_dpoolsize(), sizeof(char*));
    int file_cur_idx = 0;
    int dir_cur_idx = 0;
    combo_pool_idx = 0;
    bool root_files = true;
    while (file_cur_idx < get_fpoolsize() && dir_cur_idx < get_dpoolsize()) {
        if (root_files) {
            while (file_cur_idx < get_fpoolsize() && tmp_fpool[file_cur_idx][1] == 'f') {
                bfs_fd_pool[combo_pool_idx] = tmp_fpool[file_cur_idx];
                ++combo_pool_idx;
                ++file_cur_idx;
            }
            root_files = false;
        }
        if (file_cur_idx < get_fpoolsize() && dir_cur_idx < get_dpoolsize() && 
                is_prefix(tmp_dpool[dir_cur_idx], tmp_fpool[file_cur_idx])) {
            bfs_fd_pool[combo_pool_idx] = tmp_dpool[dir_cur_idx];
            ++combo_pool_idx;
            bfs_fd_pool[combo_pool_idx] = tmp_fpool[file_cur_idx];
            ++combo_pool_idx;
            ++file_cur_idx;
            while(file_cur_idx < get_fpoolsize() && 
                    is_prefix(tmp_dpool[dir_cur_idx], tmp_fpool[file_cur_idx])) {
                bfs_fd_pool[combo_pool_idx] = tmp_fpool[file_cur_idx];
                ++combo_pool_idx;
                ++file_cur_idx;
            }
            ++dir_cur_idx;
        }
    }
    while (dir_cur_idx < get_dpoolsize()) {
        bfs_fd_pool[combo_pool_idx] = tmp_dpool[dir_cur_idx];
        ++combo_pool_idx;
        ++dir_cur_idx;
    }
}
#endif

/* TODO: Do we need to handle basepaths, testdirs, and testfiles? */
static void free_all_globals() 
{
    /* Free all fickle members */
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        if (globals_t_p->fslist[i])
            free(globals_t_p->fslist[i]);
    }
    if (globals_t_p->fslist)
        free(globals_t_p->fslist);

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        if (globals_t_p->fssuffix[i])
            free(globals_t_p->fssuffix[i]);
    }
    if (globals_t_p->fssuffix)
        free(globals_t_p->fssuffix);

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        if (globals_t_p->devlist[i])
            free(globals_t_p->devlist[i]);
    }
    if (globals_t_p->devlist)
        free(globals_t_p->devlist);

    if (globals_t_p->devsize_kb)
        free(globals_t_p->devsize_kb);

    /* Free all steady members */
    if (globals_t_p->fsimgs)
        free(globals_t_p->fsimgs);
    if (globals_t_p->fsfds)
        free(globals_t_p->fsfds);
    if (globals_t_p->absfs)
        free(globals_t_p->absfs);
    if (globals_t_p->rets)
        free(globals_t_p->rets);
    if (globals_t_p->errs)
        free(globals_t_p->errs);

#ifdef FILEDIR_POOL
    /* Free file and dir pools */
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        for (int j = 0; j < globals_t_p->fpoolsize; ++j) {
            if (globals_t_p->filepool[i][j])
                free(globals_t_p->filepool[i][j]);
        }
        if (globals_t_p->filepool[i])
            free(globals_t_p->filepool[i]);

        for (int j = 0; j < globals_t_p->dpoolsize; ++j) {
            if (globals_t_p->directorypool[i][j])
                free(globals_t_p->directorypool[i][j]);
        }
        if (globals_t_p->directorypool[i])
            free(globals_t_p->directorypool[i]);
    }
    free(globals_t_p->filepool);
    free(globals_t_p->directorypool);
#endif

    /* Free global structure pointer */
    if (globals_t_p)
        free(globals_t_p);

    /* Free globals arguments */
    if (global_args)
        free(global_args);
}

static int cli_or_env_args(int argc, char *argv[])
{
    if (argc < 3) {
        fprintf(stderr, "Too few arguments.  Usage: ./pan -K args\n");
        return -1;
    }
    bool opt_found = false;
    size_t len = 0;
    while (argc > 1 && argv[1][0] == '-')
    {
        switch (argv[1][1]) {
            case 'K':
                if (opt_found) {
                    fprintf(stderr, "Multiple global arguments not allowed!");
                    return -1;
                }
                argv++;
                argc--;
                len = snprintf(NULL, 0, "%s", argv[1]);
                global_args = calloc(len + 1, sizeof(char));
                snprintf(global_args, len + 1, "%s", argv[1]);
                opt_found = true;
            default:
                break;
        }
        argc--;
        argv++;
    }
    if (!global_args || len == 0) {
        fprintf(stderr, "No global arguments found!\n");
        return -1;
    }
    /* return 0 indicates use environment var */
    if (len == 1)
        return 0; 
    /* return 1 indicates use command-line arguments */
    return 1;
}

static void dump_all_globals()
{
    FILE * fp;
    char dump_fn[MAX_FS + 10];
    sprintf(dump_fn, "dump_globals_%u.log", globals_t_p->_swarm_id);
    fp = fopen (dump_fn, "w");
    if (!fp) {
        fprintf(stderr, "Error opening file %s\n", dump_fn);
        exit(1);
    }
    fprintf(fp, "swarm_id: %u\n", globals_t_p->_swarm_id);
    fprintf(fp, "n_fs: %u\n", globals_t_p->_n_fs);
    for(int i = 0; i < globals_t_p->_n_fs; ++i) {
        fprintf(fp, "fs index: %d\n", i);
        fprintf(fp, "fs:%s\tsuffix:%s\tdevice:%s\tdevszkb:%ld\n", 
            globals_t_p->fslist[i], globals_t_p->fssuffix[i], 
            globals_t_p->devlist[i], globals_t_p->devsize_kb[i]);
    }
    fclose(fp);
}

#ifdef FILEDIR_POOL
static void dump_file_dir_pools()
{
    FILE * fp;
    char dump_fn[PATH_MAX];
    sprintf(dump_fn, "dump_fdpools_%u.log", globals_t_p->_swarm_id);
    fp = fopen(dump_fn, "w");
    if (!fp) {
        fprintf(stderr, "Error opening file %s\n", dump_fn);
        exit(1);
    }
    fprintf(fp, "swarm_id: %u\n", globals_t_p->_swarm_id);
    fprintf(fp, "n_fs: %u\n\n", globals_t_p->_n_fs);
    // dump the pool information
    fprintf(fp, "File pool size: %d\n", globals_t_p->fpoolsize);
    fprintf(fp, "Directory pool size: %d\n", globals_t_p->dpoolsize);

    fprintf(fp, "--- FILE POOL ---\n");
    for (int i = 0; i < get_n_fs(); ++i) {
        fprintf(fp, "File system %d: \n", i + 1);
        for (int j = 0; j < globals_t_p->fpoolsize; ++j) {
            fprintf(fp, "%s\n", get_filepool()[i][j]);
        }
    }
    fprintf(fp, "\n");
    fprintf(fp, "--- DIRECTORY POOL ---\n");
    for (int i = 0; i < get_n_fs(); ++i) {
        fprintf(fp, "File system %d: \n", i + 1);
        for (int j = 0; j < globals_t_p->dpoolsize; ++j) {
            fprintf(fp, "%s\n", get_directorypool()[i][j]);
        }
    }
    fprintf(fp, "\n");
    fclose(fp);
}
#endif

void __attribute__((constructor)) globals_init(int argc, char *argv[])
{
    int ret = -1;
    /* Read command-line option and decide CLI or ENV */
    opt_ret = cli_or_env_args(argc, argv);
    if (opt_ret < 0) {
        fprintf(stderr, "Cannot decide cli or env for globals.\n");
        exit(EXIT_FAILURE);
    }
    /* Init a global structure pointer */
    init_globals_pointer();
    /* Process enviroment variable */
    if (opt_ret == 0) {
        ret = get_mcfs_env_arguments();
    }
    /* Process CLI options */
    else if (opt_ret == 1) {
        ret = get_mcfs_cli_arguments();
    }
    if (ret < 0) {
        fprintf(stderr, "Error occurred while parsing arguments: %d\n", ret);
    }
    /* Get devices and file system suffixes */
    prepare_dev_suffix();
    /* Initialize fslist and devsize_kb */
    init_all_fickle_globals();
    /* Initialize other global data */
    init_all_steady_globals();
    /* Initialize basepaths (mountpoints) */
    init_basepaths();
#ifdef FILEDIR_POOL
    /* Initialize parameters related multi-file and multi-dir structure */
    init_multi_files_params();
    /* BFS the file and dir pools and get a combo pool */
    build_bfs_fdcombo_pool();
    /* (default commented out) Dump file dir pools: dump_fd_pools_0.log */
    dump_file_dir_pools();
#endif
    /* Initialize fs_frozen status flags*/
    fs_frozen = calloc(get_n_fs(), sizeof(bool));
    if (!fs_frozen)
        mem_alloc_err();
    dump_all_globals();
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) globals_cleanup(void)
{
    free_all_globals();
    if (fs_frozen)
        free(fs_frozen);
}

