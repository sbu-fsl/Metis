#include "init_globals.h"

globals_t *globals_t_p;

bool *fs_frozen;

static char *mcfs_globals_env;
static const char *mcfs_globals_env_key = "MCFS_FSLIST";
static const char *globals_delim = ":";
static const char *ramdisk_name = "ram";
static const char *mtdblock_name = "mtdblock";

static char *fslist_to_copy[MAX_FS];
static size_t devsize_kb_to_copy[MAX_FS];
static char *global_args = NULL;
static int opt_ret = -1;

dev_nums_t dev_nums = {.all_rams = 0, .all_mtdblocks = 0};

/*
 * current is the list of directories previous depth
 * size is current's size.
 */
static void pool_dfs(int directorycount, int filecount, int path_depth, int max_name_len, char** current, int size) {
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
        for (int j = 0; j < directorycount; j++) {
            append = max_name_len - 2;
            size_t len = snprintf(NULL, 0, "%s/d-%0*d", current[i], append, j);
            newpool[newnames_len] = calloc(1, 1 + len);
            snprintf(newpool[newnames_len], 1 + len, "%s/d-%0*d", current[i], append, j);

            get_directorypool()[get_dirpool_idx()] = calloc(1, 1 + len);
            snprintf(get_directorypool()[get_dirpool_idx()], 1 + len, "%s/d-%0*d", current[i], append, j);
            globals_t_p->dirpool_idx++;
            newnames_len++;
        }
    }

    /* 
     * Iterate through directories in the previous depth(stored in current)
     * append "f-j" to current[i] and add to filepool
     */
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < filecount; j++) {
            append = max_name_len - 2;
            size_t len = snprintf(NULL, 0, "%s/f-%0*d", current[i], append, j);

            get_filepool()[get_filepool_idx()] = calloc(1, 1+len);
            snprintf(get_filepool()[get_filepool_idx()], 1+len, "%s/f-%0*d", current[i], append, j);
            globals_t_p->filepool_idx++;
        }
        free(current[i]);
    }
    if(path_depth == 1){
        return;
    }

    pool_dfs(directorycount, filecount, path_depth-1, max_name_len, newpool, newnames_len);
}

static int getpowsum(int directorycount, int path_depth) {
    int sum = 0;
    int current = 1;
    for(int i = 0; i < path_depth; i++){
        current *= directorycount;
        sum += current;
    }
    return sum;
}

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
        fprintf(stderr, "Incorrect args format! Exp: 0:fs1:size1:fs2:size2\n");
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
            fprintf(stderr, "File system type not supported for device\n");
            exit(EXIT_FAILURE);
        }
        else if (strcmp(dev_all[dev_idx], ramdisk_name) == 0) {
            ++dev_nums.all_rams;
        }
        else if (strcmp(dev_all[dev_idx], mtdblock_name) == 0) {
            ++dev_nums.all_mtdblocks;
        }
    }
    dev_idx = -1;

    /* populate device name (including orginal and used dev names) */
    size_t len;
    int ram_cnt = 0, mtdblock_cnt = 0;
    int ram_id = -1, mtdblock_id = -1;

    globals_t_p->devlist = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->devlist) 
        mem_alloc_err();
    globals_t_p->fssuffix = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->fssuffix) 
        mem_alloc_err();
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        dev_idx = get_dev_from_fs(fslist_to_copy[i]);
        if (dev_idx == -1) {
            globals_t_p->devlist[i] = calloc(1, sizeof(char));
            memset(globals_t_p->devlist[i], '\0', sizeof(char));
        }
        else if (strcmp(dev_all[dev_idx], ramdisk_name) == 0) {
            if (globals_t_p->_swarm_id >= 1)
                ram_id = ram_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_rams;
            else 
                ram_id = ram_cnt;
            len = snprintf(NULL, 0, "/dev/%s%d", ramdisk_name, ram_id);
            globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
            snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", ramdisk_name, ram_id);
            ++ram_cnt;
        }
        else if (strcmp(dev_all[dev_idx], mtdblock_name) == 0) {
            if (globals_t_p->_swarm_id >= 1)
                mtdblock_id = mtdblock_cnt + (globals_t_p->_swarm_id - 1) * dev_nums.all_mtdblocks;
            else
                mtdblock_id = mtdblock_cnt;
            len = snprintf(NULL, 0, "/dev/%s%d", mtdblock_name, mtdblock_id);
            globals_t_p->devlist[i] = calloc(len + 1, sizeof(char));
            snprintf(globals_t_p->devlist[i], len + 1, "/dev/%s%d", mtdblock_name, mtdblock_id);
            ++mtdblock_cnt;
        }
        /* Populate fs suffix -- format -$fsid-$swarmid */
        len = snprintf(NULL, 0, "-i%d-s%d", i, globals_t_p->_swarm_id);
        globals_t_p->fssuffix[i] = calloc(len + 1, sizeof(char));
        snprintf(globals_t_p->fssuffix[i], len + 1, "-i%d-s%d", i, globals_t_p->_swarm_id);
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
        memcpy(globals_t_p->fslist[i], fslist_to_copy[i], strlen(fslist_to_copy[i]) + 1);
        free(fslist_to_copy[i]);
    }

    /* devsize_kb */
    globals_t_p->devsize_kb = calloc(globals_t_p->_n_fs, sizeof(size_t));
    if (!globals_t_p->devsize_kb)
        mem_alloc_err(); 
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        memcpy(globals_t_p->devsize_kb, devsize_kb_to_copy, sizeof(size_t) * (globals_t_p->_n_fs));
    }
}

static void init_all_steady_globals() 
{
    /* basepaths */
    globals_t_p->basepaths = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->basepaths) 
        mem_alloc_err();

    /* testdirs */
    globals_t_p->testdirs = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testdirs) 
        mem_alloc_err();

    /* testfiles */
    globals_t_p->testfiles = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testfiles) 
        mem_alloc_err();

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
}

static void init_multi_files_params()
{
    /* filecount */
    globals_t_p->filecount = 1;

    /* directorycount */
    globals_t_p->directorycount = 2;

    /* filepool_idx */
    globals_t_p->filepool_idx = 0;

    /* dirpool_idx */
    globals_t_p->dirpool_idx = 0;

    /* path_depth */
    globals_t_p->path_depth = 3;

    /* max_name_len */
    globals_t_p->max_name_len = 10;

    char *current[PATH_MAX];
    int directorypool_size = 0;
    int filepool_size = 0;
    if (globals_t_p->directorycount > 0) {
        /*
         * Directory pool size  = no. of directories at depth 0 + no. of directories at depth 1 + .....
         * = directorycount + (no. of directories at depth 0)*directorycount + (no. of directories at depth 1)*directory count + ...
         * = directorycount + directorycount*directorycount + directorycount*directorycount*directorycount + .....
         *
         * Similarly, file pool size = no. of files at depth 0 + no. of files at depth 1 + ....
         * = filecount + (no. of directories at depth 0)*filecount + (no. of directories at depth 1)*filecount + ...
         * = filecount * ( 1 + (no. of directories at depth 0) + (no. of directories at depth 1) + ....) 
         * = filecount * (directorypool_size / directorycount);
         */
        directorypool_size = getpowsum(globals_t_p->directorycount, globals_t_p->path_depth);
        filepool_size = globals_t_p->filecount * (directorypool_size / globals_t_p->directorycount);
    }
    else {
        filepool_size = globals_t_p->filecount;
    }

    /* filepool */
    globals_t_p->filepool = calloc(filepool_size, sizeof(char*));

    /* directorypool */
    globals_t_p->directorypool = calloc(directorypool_size, sizeof(char*));

    size_t len = 0;
    current[0] = calloc(1, len + 1);

    if (get_pool_depth() > 0) {
        pool_dfs(globals_t_p->directorycount, globals_t_p->filecount, 
            globals_t_p->path_depth, globals_t_p->max_name_len, current, 1);
    }
}

/* TODO 1: Do we need to handle basepaths, testdirs, and testfiles? */
/* TODO 2: Free memory for file pool and directory pool. */
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

    /* Free global structure pointer */
    if (globals_t_p)
        free(globals_t_p);

    /* Free globals arguments */
    if (global_args)
        free(global_args);
}

unsigned int get_n_fs()
{
    return globals_t_p->_n_fs;
}

char **get_fslist()
{
    return globals_t_p->fslist;
}

char **get_fssuffix()
{
    return globals_t_p->fssuffix;
}

char **get_devlist()
{
    return globals_t_p->devlist;
}

size_t *get_devsize_kb()
{
    return globals_t_p->devsize_kb;
}

char **get_basepaths()
{
    return globals_t_p->basepaths;
}

char **get_testdirs()
{
    return globals_t_p->testdirs;
}

char **get_testfiles()
{
    return globals_t_p->testfiles;
}

void **get_fsimgs()
{
    return globals_t_p->fsimgs;
}

int *get_fsfds()
{
    return globals_t_p->fsfds;
}

absfs_state_t *get_absfs()
{
    return globals_t_p->absfs;
}

int *get_rets()
{
    return globals_t_p->rets;
}

int *get_errs()
{
    return globals_t_p->errs;
}

int get_filecount()
{
    return globals_t_p->filecount;
}

int get_directorycount()
{
    return globals_t_p->directorycount;
}

int get_filepool_idx()
{
    return globals_t_p->filepool_idx;
}

int get_dirpool_idx()
{
    return globals_t_p->dirpool_idx;
}

int get_pool_depth()
{
    return globals_t_p->path_depth;
}

int get_max_name_len()
{
    return globals_t_p->max_name_len;
}

char **get_filepool()
{
    return globals_t_p->filepool;
}

char **get_directorypool()
{
    return globals_t_p->directorypool;
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

static void dump_file_dir_pools()
{
    FILE * fp;
    char dump_fn[PATH_MAX];
    sprintf(dump_fn, "dump_file_dir_pools_%u.log", globals_t_p->_swarm_id);
    fp = fopen(dump_fn, "w");
    fprintf(fp, "swarm_id: %u\n", globals_t_p->_swarm_id);
    fprintf(fp, "n_fs: %u\n\n", globals_t_p->_n_fs);
    // dump the pool information
    fprintf(fp, "filepool_idx: %d\n", get_filepool_idx());
    fprintf(fp, "dirpool_idx: %d\n", get_dirpool_idx());

    fprintf(fp, "FILE POOL:\n");
    for (int i = 0; i < get_filepool_idx(); ++i) {
        fprintf(fp, "%s\n", get_filepool()[i]);
    }
    fprintf(fp, "\n");
    fprintf(fp, "DIRECTORY POOL:\n");
    for (int i = 0; i < get_dirpool_idx(); ++i) {
        fprintf(fp, "%s\n", get_directorypool()[i]);
    }
    fprintf(fp, "\n");
    fclose(fp);
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
    /* Initalize fslist and devsize_kb */
    init_all_fickle_globals();
    /* Initalize other global data */
    init_all_steady_globals();
    /* Initalize parameters related multi-file and multi-dir structure */
    init_multi_files_params();
    /* Dump the file and dir pools */
    dump_file_dir_pools();
    /* Initalize fs_frozen status flags*/
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
