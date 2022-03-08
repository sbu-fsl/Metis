#include "init_globals.h"

globals_t *globals_t_p;
static const char *fslist_to_copy[] = {"ext4", "jffs2"};
static const char *fssuffix_to_copy[] = {"", ""};
static const char *devlist_to_copy[] = {"/dev/ram0", "/dev/mtdblock0"};
static const size_t devsize_kb_to_copy[] = {256, 256};

static void init_all_fickle_globals() 
{
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }
    /* _n_fs */
    globals_t_p->_n_fs = 2;

    /* fslist */
    globals_t_p->fslist = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->fslist) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }
    // each string in fslist 
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->fslist[i] = calloc(strlen(fslist_to_copy[i]) + 1, 
                                        sizeof(char));
        if (!globals_t_p->fslist[i]) {
            mem_alloc_err();
            exit(EXIT_FAILURE);       
        }
        memcpy(globals_t_p->fslist[i], fslist_to_copy[i], 
                strlen(fslist_to_copy[i]) + 1);
    }

    /* fssuffix */
    globals_t_p->fssuffix = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->fssuffix) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }  
    // each string in fssuffix
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->fssuffix[i] = calloc(strlen(fssuffix_to_copy[i]) + 1, 
                                        sizeof(char));
        if (!globals_t_p->fssuffix[i]) {
            mem_alloc_err();
            exit(EXIT_FAILURE);       
        }        
        memcpy(globals_t_p->fssuffix[i], fssuffix_to_copy[i], 
                strlen(fssuffix_to_copy[i]) + 1);
    }

    /* devlist */
    globals_t_p->devlist = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->devlist) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }  
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->devlist[i] = calloc(strlen(devlist_to_copy[i]) + 1, 
                                        sizeof(char));        
        if (!globals_t_p->devlist[i]) {
            mem_alloc_err();
            exit(EXIT_FAILURE);       
        }        
        memcpy(globals_t_p->devlist[i], devlist_to_copy[i], 
                strlen(devlist_to_copy[i]) + 1);
    }

    /* devsize_kb */
    globals_t_p->devsize_kb = calloc(globals_t_p->_n_fs, sizeof(size_t));
    if (!globals_t_p->devsize_kb) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }  
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        memcpy(globals_t_p->devsize_kb, devsize_kb_to_copy, 
                sizeof(size_t) * (globals_t_p->_n_fs));
    }
}

static void init_all_steady_globals() 
{
    /* basepaths */
    globals_t_p->basepaths = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->basepaths) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }

    /* testdirs */
    globals_t_p->testdirs = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testdirs) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }

    /* testfiles */
    globals_t_p->testfiles = calloc(globals_t_p->_n_fs, sizeof(char*));
    if (!globals_t_p->testfiles) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }

    /* fsimgs */
    globals_t_p->fsimgs = calloc(globals_t_p->_n_fs, sizeof(void*));
    if (!globals_t_p->fsimgs) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }

    /* fsfds */
    globals_t_p->fsfds = calloc(globals_t_p->_n_fs, sizeof(int));
    if (!globals_t_p->fsfds) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }
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
    free(globals_t_p->basepaths);
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->basepaths[i]);
    }

    free(globals_t_p->testdirs);
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->testdirs[i]);
    }

    free(globals_t_p->testfiles);
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->testfiles[i]);
    }

    free(globals_t_p->fsimgs);
    free(globals_t_p->fsfds);

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

void __attribute__((constructor)) globals_init()
{
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
