#include "init_globals.h"

globals_t *globals_t_p;

static char *mcfs_globals_env;
static const char *mcfs_globals_env_key = "MCFS_FSLIST";
static const char *globals_delim = ":";
static const char *ramdisk_name = "ram";
static const char *mtdblock_name = "mtdblock";

static char *fslist_to_copy[MAX_FS];
static size_t devsize_kb_to_copy[MAX_FS];

dev_nums_t dev_nums = {.all_rams = 0, .all_mtdblocks = 0};

static void init_globals_pointer()
{
    /* global structure pointer */
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p)
        mem_alloc_err();
}

static int get_mcfs_env_arguments() 
{
    char globals_used_env_key[ENV_KEY_MAX];
    // No swarm mode, let's use MCFS_FSLIST0
    globals_t_p->_swarm_id = 0;

    // USE MCFS_FSLIST${SWARMID} as env name
#if defined SWARMID && SWARMID >= 1
    globals_t_p->_swarm_id = SWARMID;
#endif
    sprintf(globals_used_env_key, "%s%u", mcfs_globals_env_key, globals_t_p->_swarm_id);

    mcfs_globals_env = getenv(globals_used_env_key);
    /* Validate existence of environment vars */
    if (!mcfs_globals_env) {
        fprintf(stderr, "globals env %s is not set.\n", globals_used_env_key);
        return -EINVAL;
    }

    /* context variable pointer for strtok_r */
    char *context = NULL;
    /* Parsing the MCFS options from env */
    int tok_cnt = 0;
    /* Example: 0:ext4:256:jffs2:512 swarm_id:fs1:size1(inKB):fs2:size2 */
    char *token = strtok_r(mcfs_globals_env, globals_delim, &context);
    while (token != NULL) {
        if (tok_cnt % 2 == 0) { // file system name
            fslist_to_copy[tok_cnt / 2] = calloc(strlen(token) + 1, sizeof(char));
            if (!fslist_to_copy[tok_cnt / 2])
                mem_alloc_err();
            strcpy(fslist_to_copy[tok_cnt / 2], token);
        }
        else { // device size
            devsize_kb_to_copy[tok_cnt / 2] = atoi(token);
        }
        ++tok_cnt;
        token = strtok_r(NULL, globals_delim, &context);
    }
    if (tok_cnt % 2 != 0) {
        fprintf(stderr, "In correct env var format! exp: fs1:size1:fs2:size2 \n");
        return -EINVAL; 
    }
    /* _n_fs */
    globals_t_p->_n_fs = tok_cnt / 2;
    return 0;
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
    // each string in fslist 
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


static void free_all_globals() 
{
    /* Free all fickle members */
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->fslist[i]);
    }
    free(globals_t_p->fslist);

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->fssuffix[i]);
    }
    free(globals_t_p->fssuffix);

    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->devlist[i]);
    }
    free(globals_t_p->devlist);

    free(globals_t_p->devsize_kb);

    /* Free all steady members */
    /* TODO: Do we need to handle basepaths, testdirs, and testfiles*/
    
    free(globals_t_p->fsimgs);
    free(globals_t_p->fsfds);
    free(globals_t_p->absfs);
    free(globals_t_p->rets);
    free(globals_t_p->errs);

    /* Free global structure pointer */
    free(globals_t_p);
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

void __attribute__((constructor)) globals_init()
{
    init_globals_pointer();
    get_mcfs_env_arguments();
    prepare_dev_suffix();
    init_all_fickle_globals();
    init_all_steady_globals();
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) globals_cleanup()
{
    free_all_globals();
}
