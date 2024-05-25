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
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ftw.h>
#include <assert.h>
#include <stdint.h>
#include <stdarg.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/ioctl.h>
#include <sys/xattr.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <openssl/md5.h>
#include <stddef.h>
#include <sys/types.h>
#include <math.h>
#include <limits.h>
#include <openssl/opensslv.h>

//From abstract_fs.h
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
#include <openssl/evp.h>
#else
#include <openssl/md5.h>
#endif
#include <dirent.h>

//From nanotiming.h
#ifdef __MACH__
#include <mach/clock.h>
#include <mach/mach.h>
#else
#include <time.h>
#include <sys/time.h>
#endif

//From operations.h
/* Max length of function name in log */
#define FUNC_NAME_LEN    16

#ifndef MAX_FS
#define MAX_FS      20
#endif

#ifndef MAX_DIR_NUM
#define MAX_DIR_NUM 200
#endif

//From vector.h
#define DEFAULT_INITCAP 16

#ifndef PATH_MAX
#define PATH_MAX    4096
#endif

/* File/Dir Pool Related Configurations */
#ifdef FILEDIR_POOL
#define FILE_COUNT 3
#define DIR_COUNT 2
#define PATH_DEPTH 2
#define MCFS_NAME_LEN 4

char **bfs_fd_pool;
int combo_pool_idx;
static int fpool_idx = 0;
static int dpool_idx = 0;
/* Temp file and dir pools are freed in precreate_pools */
static char **tmp_fpool = NULL;
static char **tmp_dpool = NULL;
#endif

struct vector {
    unsigned char *data;
    size_t unitsize;
    size_t len;
    size_t capacity;
};

int pre = 0;
int seq = 0;

typedef struct vector vector_t;

static inline void _vector_init(struct vector *vec, size_t unitsize, size_t initcap) {
    if (initcap < DEFAULT_INITCAP)
        initcap = DEFAULT_INITCAP;
    vec->unitsize = unitsize;
    vec->len = 0;
    vec->capacity = initcap;
    vec->data = (unsigned char *)calloc(initcap, unitsize);
}
#define vector_init_2(vec, type)    _vector_init(vec, sizeof(type), DEFAULT_INITCAP)
#define vector_init_3(vec, type, initcap)   _vector_init(vec, sizeof(type), initcap)
#define vector_init_x(a, b, c, func, ...)   func
/* Macro function with optional arg: vector_init(struct vector *vec, type, [initcap=16]) */
#define vector_init(...)    vector_init_x(__VA_ARGS__,\
                                          vector_init_3(__VA_ARGS__),\
                                          vector_init_2(__VA_ARGS__)\
                                         )

static inline int vector_expand(struct vector *vec) {
    size_t newcap = vec->unitsize * vec->capacity * 2;
    unsigned char *newptr = (unsigned char *)realloc(vec->data, newcap);
    if (newptr == NULL)
        return ENOMEM;
    vec->data = newptr;
    vec->capacity *= 2;
    return 0;
}

static inline int vector_add(struct vector *vec, void *el) {
    int ret;
    if (vec->len >= vec->capacity) {
        if ((ret = vector_expand(vec)) != 0)
            return ret;
    }
    size_t offset = vec->len * vec->unitsize;
    memcpy(vec->data + offset, el, vec->unitsize);
    vec->len++;
    return 0;
}

static inline void *_vector_get(struct vector *vec, size_t index) {
    if (index < 0 || index >= vec->len)
        return NULL;
    return (void *)(vec->data + index * vec->unitsize);
}
#define vector_get(vec, type, index) \
    (type *)_vector_get(vec, index)

static inline void *_vector_peek_top(struct vector *vec) {
    if (vec->len == 0)
        return NULL;
    return (void *)(vec->data + (vec->len - 1) * vec->unitsize);
}
#define vector_peek_top(vec, type) \
    (type *)_vector_peek_top(vec)

static inline void vector_try_shrink(struct vector *vec) {
    if (vec->len >= vec->capacity / 2)
        return;
    if (vec->len <= DEFAULT_INITCAP)
        return;
    size_t newcap = vec->capacity / 2 * vec->unitsize;
    vec->data = (unsigned char *)realloc(vec->data, newcap);
}

static inline void vector_destroy(struct vector *vec) {
    free(vec->data);
    memset(vec, 0, sizeof(struct vector));
}

#define vector_iter(vec, type, entry) \
    int _i; \
    for (entry = (type *)((vec)->data), _i = 0; _i < (vec)->len; ++_i, ++entry)

#ifdef __cplusplus
extern "C" {
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
//   int all_loops;
} dev_nums_t;

static const char *fs_all[] = {"ext4","jfs"};
                               
static const char *dev_all[]= {"ram","ram"};

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
    /* Fields related to new operations and dir structure */
    int fpoolsize;
    int dpoolsize;
    /* Fields on xattr */
    char **xfpaths;
} globals_t;

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

static inline int get_fpoolsize() {
    return globals_t_p->fpoolsize;
}

static inline int get_dpoolsize() {
    return globals_t_p->dpoolsize;
}

static inline char **get_xfpaths() {
    return globals_t_p->xfpaths;
}

#ifdef __cplusplus
}
#endif

static const char *globals_delim = ":";
static const char *ramdisk_name = "ram";

static char *fslist_to_copy[MAX_FS];
static size_t devsize_kb_to_copy[MAX_FS];
static char *global_args = NULL;
static int opt_ret = -1;

dev_nums_t dev_nums = {.all_rams = 0};

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
    }
    dev_idx = -1;

    /* populate device name (including orginal and used dev names) */
    size_t len;
    int ram_cnt = 0, ram_id = -1;

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

    size_t len = 0;
    current[0] = calloc(1, len + 1);

    if (PATH_DEPTH > 0) {
        pool_dfs(PATH_DEPTH, current, 1);
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
    
    /* Process CLI options */
    if (opt_ret == 1) {
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
#endif
    /* Initialize fs_frozen status flags*/
    fs_frozen = calloc(get_n_fs(), sizeof(bool));
    if (!fs_frozen)
        mem_alloc_err();
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

extern char func[FUNC_NAME_LEN + 1];

#define min(x, y) ((x >= y) ? y : x)

enum fill_type {PATTERN, ONES, BYTE_REPEAT, RANDOM_EACH_BYTE};

/* Generate data into a given buffer.
 * @value: 0-255 for uniform characters, -1 for random filling */
static inline void generate_data(char *buffer, size_t len, size_t offset, enum fill_type type, int value)
{
    switch (type) {
    /* ONES: write all byte 1 */
    case ONES:
        memset(buffer, 1, len);
        break;
    /* BYTE_REPEAT: select a random byte but write this byte uniformly */
    case BYTE_REPEAT:
        memset(buffer, value, len);
        break;
    /* PATTERN: write the bytes that are the same as the value of offsets */
    case PATTERN:
    {
        int new_offset = 3 - offset % sizeof(int);
        for (int i = 0; i < new_offset; i++) {
            buffer[i] = 0;
        }
        int *ip = (int *) (buffer + new_offset);
        for (int i = 0; i <= len / sizeof(int); i++) {
            ip[i] = offset / sizeof(int) + i;
        }
        break;
    }
    /* RANDOM_EACH_BYTE: write random value for each int size (4 bytes) */
    case RANDOM_EACH_BYTE:
    {
        size_t i = 0, remaining = len;
        int n = rand();
        while (remaining > 0) {
            int *ptr = (int *)(buffer + i);
            *ptr = n;
            remaining -= min(sizeof(int), remaining);
            i += min(sizeof(int), remaining);
        }
        break;
    }
    }
}

static inline ssize_t fsize(int fd)
{
    struct stat info;
    int ret = fstat(fd, &info);
    if (ret != 0)
        return -1;
    if (info.st_mode & S_IFREG) {
        // verify st_size is even multiple of 4096
        const size_t bs = 4096;
        if (info.st_size % bs != 0)
            return -1;
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return -1;
        return devsz;
    } else {
        return -1;
    }
}

void unmount_all(bool strict);
void record_fs_stat();

static inline void unmount_all_strict()
{
    unmount_all(true);
}

static inline void unmount_all_relaxed()
{
    unmount_all(false);
}

void extract_fields(vector_t *fields_vec, char *line, const char *delim)
{
	vector_init(fields_vec, char *);
	char *field = strtok(line, delim);
	while (field) {
		size_t flen = strlen(field);
		char *field_copy = malloc(flen + 1);
		assert(field_copy);
		field_copy[flen] = '\0';
		strncpy(field_copy, field, flen);
		vector_add(fields_vec, &field_copy);
		field = strtok(NULL, ", ");
	}
}

void destroy_fields(vector_t *fields_vec)
{
	char **field;
	vector_iter(fields_vec, char *, field) {
		free(*field);
	}
	vector_destroy(fields_vec);
}

int create_file(const char *path, int flags, int mode)
{
    int fd = open(path, flags, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length)
{
    int fd = open(path, flags, O_RDWR);
    int err;
    if (fd < 0) {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit_err;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int do_create_file(vector_t *argvec)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *flagstr = *vector_get(argvec, char *, 2);
	char *modestr = *vector_get(argvec, char *, 3);
	char *endptr;
	int flags = (int)strtol(flagstr, &endptr, 8);
	int mode = (int)strtol(modestr, &endptr, 8);
	int res = create_file(filepath, flags, mode);
	printf("create_file(%s, 0%o, 0%o) -> ret=%d, errno=%s\n",
	       filepath, flags, mode, res, strerror(errno));
	return res;
}

int do_write_file(vector_t *argvec, int seq)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *flagstr = *vector_get(argvec, char *, 2);
	char *offset_str = *vector_get(argvec, char *, 4);
	char *len_str = *vector_get(argvec, char *, 5);
	char *endp;
	int flags = (int)strtol(flagstr, &endp, 8);
	off_t offset = strtol(offset_str, &endp, 10);
	size_t writelen = strtoul(len_str, &endp, 10);
	assert(offset != LONG_MAX);
	assert(writelen != ULONG_MAX);
	
	char *buffer = malloc(writelen);
	assert(buffer != NULL);
	/* This is to make sure data written to all file systems in the same
	 * group of operations is the same */
	int integer_to_write = seq / get_n_fs();
	generate_data(buffer, writelen, offset, BYTE_REPEAT, integer_to_write);
	int ret = write_file(filepath, flags, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %o, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, flags, offset, writelen, ret, strerror(err));
	free(buffer);
	return ret;
}

int do_unlink(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = unlink(path);
	int err = errno;
	printf("unlink(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
	return ret;
}

int do_mkdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	char *modestr = *vector_get(argvec, char *, 2);
	char *endp;
	int mode = (int)strtol(modestr, &endp, 8);
	int ret = mkdir(path, mode);
	int err = errno;
	printf("mkdir(%s, 0%o) -> ret=%d, errno=%s\n",
	       path, mode, ret, strerror(err));
	return ret;
}

int do_rmdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = rmdir(path);
	int err = errno;
	printf("rmdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
	return ret;
}

void populate_replay_basepaths()
{
	for (int i = 0; i < get_n_fs(); ++i) {
		size_t len = snprintf(NULL, 0, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
		get_basepaths()[i] = calloc(1, len + 1);
		snprintf(get_basepaths()[i], len + 1, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
	}
}

void mountall()
{
    int failpos, err;
    for (int i = 0; i < get_n_fs(); ++i) {
        int ret = -1;
        ret = mount(get_devlist()[i], get_basepaths()[i], get_fslist()[i], MS_NOATIME, "");     
        if (ret != 0) {
            failpos = i;
            err = errno;
            goto err;
        }
    }
    return;
err:
    /* undo mounts */
    for (int i = 0; i < failpos; ++i) {
        umount2(get_basepaths()[i], MNT_FORCE);
    }
    fprintf(stderr, "Could not mount file system %s in %s at %s (%s)\n",
            get_fslist()[failpos], get_devlist()[failpos], get_basepaths()[failpos],
            strerror(err));
    exit(1);
}

void unmount_all(bool strict)
{
    bool has_failure = false;
    int ret;
#ifndef NO_FS_STAT
    record_fs_stat();
#endif
    for (int i = 0; i < get_n_fs(); ++i) {
        // Change retry limit from 20 to 19 to avoid excessive delay
        int retry_limit = 19;
        int num_retries = 0;
        
        while (retry_limit > 0) {
            ret = umount2(get_basepaths()[i], 0);
            if (ret == 0) {
                break; // Success, exit the retry loop
            }        

            /* If unmounting failed due to device being busy, again up to
            * retry_limit times with 100 * 2^n ms (n = num_retries) */
            if (errno == EBUSY) {
                // 100 * (1 <<  0) = 100ms
                // 100 * (1 << 18) = 100 * 262144 = 26.2144s
                useconds_t waitms = 100 * (1 << num_retries); // Exponential backoff starting at 100ms
                fprintf(stderr, "File system %s mounted on %s is busy. Retry %d times,"
                        "unmounting after %dms.\n", get_fslist()[i], get_basepaths()[i], num_retries + 1,
                        waitms);
                usleep(1000 * waitms);
                num_retries++;
                retry_limit--;
            } 
            else {
                // Handle non-EBUSY errors immediately without retrying
                fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                        get_fslist()[i], get_basepaths()[i], strerror(errno));
                has_failure = true;
            }
        }
        
        if (retry_limit == 0) {
            fprintf(stderr, "Failed to unmount file system %s at %s after retries.\n",
                    get_fslist()[i], get_basepaths()[i]);
            has_failure = true;
        }
    }
    if (has_failure && strict)
        exit(1);
}


static void execute_cmd(const char *cmd)
{
    int retval = system(cmd);
    int status, signal = 0;
    if ((status = WEXITSTATUS(retval)) != 0) {
        fprintf(stderr, "Command `%s` failed with %d.\n", cmd, status);
    }
    if (WIFSIGNALED(retval)) {
        signal = WTERMSIG(retval);
        fprintf(stderr, "Command `%s` terminated with signal %d.\n", cmd,
                signal);
    }
    if (status || signal) {
        exit(1);
    }
}

int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

static int check_device(const char *devname, const size_t exp_size_kb)
{
    int fd = open(devname, O_RDONLY);
    struct stat devinfo;
    if (fd < 0) {
        fprintf(stderr, "Cannot open %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        return -errno;
    }
    int retval = fstat(fd, &devinfo);
    if (retval < 0) {
        fprintf(stderr, "Cannot stat %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        close(fd);
        return -errno;
    }
    if (!S_ISBLK(devinfo.st_mode)) {
        fprintf(stderr, "%s is not a block device.\n", devname);
        close(fd);
        return -ENOTBLK;
    }
    size_t devsize = fsize(fd);
    if (devsize < exp_size_kb * 1024) {
        fprintf(stderr, "%s is smaller than expected (expected %zu KB, "
                "got %zu).\n", devname, exp_size_kb, devsize / 1024);
        close(fd);
        return -ENOSPC;
    }
    close(fd);
    return 0; 
}

static void populate_mountpoints()
{
    char check_mount_cmdbuf[PATH_MAX];
    char unmount_cmdbuf[PATH_MAX];
    char check_mp_exist_cmdbuf[PATH_MAX];
    char rm_mp_cmdbuf[PATH_MAX];
    char mk_mp_cmdbuf[PATH_MAX];
    for (int i = 0; i < get_n_fs(); ++i) {
        snprintf(check_mount_cmdbuf, PATH_MAX, "mount | grep %s", get_basepaths()[i]);    
        /* If the mountpoint has fs mounted, then unmount it */
        if (execute_cmd_status(check_mount_cmdbuf) == 0) {
            snprintf(unmount_cmdbuf, PATH_MAX, "umount -f %s", get_basepaths()[i]);
            execute_cmd(unmount_cmdbuf);
        }
        /* 
         * Caveat: if we use file/dir pools and test in-memory file systems
         * like VeriFS, we should not remove the mount point here because
         * we need to pre-create files/dirs in the pool. Removing mountpoints
         * simply erase the precreated files/dirs.
         *
         * Also, we cannot mount VeriFS and other in-memory file systems on
         * a non-empty mount point.
         * 
         * The correct way would be removing and recreating mount point of 
         * VeriFS in the setup shell scripts before running pan.
         */

        snprintf(mk_mp_cmdbuf, PATH_MAX, "mkdir -p %s", get_basepaths()[i]);
        execute_cmd(mk_mp_cmdbuf);
    }
}

static int setup_jfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.jfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_generic(const char *fsname, const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    ret = check_device(devname, size_kb);
		        
    if (ret != 0) {
    	fprintf(stderr, "Cannot setup %s because %s is bad or not ready.\n",fsname, devname);
	return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,"dd if=/dev/zero of=%s bs=1k count=%zu status=none",devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.%s %s", fsname, devname);
    execute_cmd(cmdbuf);

    return 0;
}

void setup_filesystems()
{
    int ret;
    populate_mountpoints();

    for (int i = 0; i < get_n_fs(); ++i) {
        if (strcmp(get_fslist()[i], "jfs") == 0) {
		    ret = setup_jfs(get_devlist()[i], get_devsize_kb()[i]);
        } else {
	    	ret = setup_generic(get_fslist()[i], get_devlist()[i], get_devsize_kb()[i]);
	    }
   
    	if (ret != 0)
    	{
        	fprintf(stderr, "Cannot setup %s file system (ret = %d)\n", get_fslist()[i], ret);
         	exit(1);
    	}
    }
}

int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode)
{
    const size_t len = strlen(path);
    char _path[PATH_MAX];
    char *p; 

    errno = 0;

    /* Copy string so its mutable */
    if (len > sizeof(_path)-1) {
        errno = ENAMETOOLONG;
        return -1; 
    }   
    strcpy(_path, path);

    bool next_f = false;
    bool next_d = false;
    /* Iterate the string */
    for (p = _path + 1; *p; p++) {
        if (*p == '/') {
            /* Temporarily truncate */
            *p = '\0';
            if (mkdir(_path, dir_mode) != 0) {
                if (errno != EEXIST) {
                    return -1; 
                }
            }
            
            *p = '/';

            if (*(p + 1) == 'f')
                next_f = true;
            else if (*(p + 1) == 'd')
                next_d = true;
        }
    }
    if (next_f) {
        int fd = creat(_path, file_mode);
        if (fd >= 0) {
            close(fd);
        }
        else if (errno != EEXIST) {
            return -1;
        }
    }
    if (next_d) {
        if (mkdir(_path, dir_mode) != 0) {
            if (errno != EEXIST) {
                return -1; 
            }
        }
    }

    return 0;
}
/* 
 * NOTE: NEED TO RECOMPILE REPLAYER "make replayer" every time we run it.
 *
 * Make sure the required devices are already set up with correct sizes. 
 *
 * Before running this program, make sure the devices are already set 
 * up with correct sizes.
 * We need to specify a sequence.log file (the sequence of operations 
 * to be replayed)
 * and a dump_prepopulate_*.log file (precreated files and dirs).
 * Usage: 
 *		sudo ./replay -K 0:ext4:256:jfs:16384 2>&1 > replay_jfs.log
 *		sudo ./replay -K 0:ext4:256:nilfs2:1028
 *		sudo ./replay -K 0:nilfs2:1028
 */
int main(int argc, char **argv)
{
	/* 
	 * Open the dump_prepopulate_*.log files to create the pre-populated
	 * files and directories.
	 */
	char *dump_prepopulate_file_name = "dump_prepopulate_0_kh6.log";
    char *sequence_log_file_name = "sequence-pan-20240209-182859-244192_kh6.log";

    FILE *pre_fp = fopen(dump_prepopulate_file_name, "r");
	
	if (!pre_fp) {
		printf("Cannot open %s. Does it exist?\n", dump_prepopulate_file_name);
		exit(1);
	}
	
	/* Open sequence file */
	FILE *seqfp = fopen(sequence_log_file_name, "r");
	
	if (!seqfp) {
		printf("Cannot open %s. Does it exist?\n", sequence_log_file_name);
		exit(1);
	}

	ssize_t len, pre_len;
	size_t linecap = 0, pre_linecap = 0;
	char *linebuf = NULL, *pre_linebuf = NULL;

	/* Populate mount points and mkfs the devices */
	setup_filesystems();
	/* Create the pre-populated files and directories */
	mountall();
	while ((pre_len = getline(&pre_linebuf, &pre_linecap, pre_fp)) >= 0) {
		char *line = malloc(pre_len + 1);
		line[pre_len] = '\0';
		strncpy(line, pre_linebuf, pre_len);
		/* remove the newline character */
		if (line[pre_len - 1] == '\n')
			line[pre_len - 1] = '\0';
		printf("pre=%d \n", pre);
		/* parse the line for pre-populated files and directories */
		size_t pre_path_len;
		char *pre_path_name;
		for (int i = 0; i < get_n_fs(); ++i) {
			pre_path_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], line);
			pre_path_name = calloc(1, pre_path_len + 1);
			snprintf(pre_path_name, pre_path_len + 1, "%s%s", get_basepaths()[i], line);
			// printf("pre_path_name=%s\n", pre_path_name);
			int ret = -1;
			ret = mkdir_p(pre_path_name, 0755, 0644);
			if (ret < 0) {
				fprintf(stderr, "mkdir_p error happened!\n");
				exit(EXIT_FAILURE);
			}
			free(pre_path_name);
		}
		pre++;
	}
	unmount_all_strict();
	/* Replay the actual operation sequence */
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d \n", seq);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);

		mountall();
		
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
			do_write_file(&argvec, seq);
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(&argvec);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(&argvec);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(&argvec);
		} else if (strncmp(funcname, "checkpoint", len) == 0 || strncmp(funcname, "restore", len) == 0) {
			seq--;
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		
		seq++;

		unmount_all_strict();
		errno = 0;
		free(line);
		destroy_fields(&argvec);
	}
	/* Clean up */
	fclose(pre_fp);
	fclose(seqfp);
	free(pre_linebuf);
	free(linebuf);

	return 0;
}
