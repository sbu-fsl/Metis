#include "init_globals.h"

globals_t *globals_t_p;

void init_all_globals() {
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p) {
        fprintf(stderr, "memory allocation failed: %s:%d:%s\n", 
            __FILE__, __LINE__, __func__);
        exit(EXIT_FAILURE);
    }
    // _n_fs
    globals_t_p->_n_fs = 2;

    // fslist
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        globals_t_p->fslist[i] = calloc(1, FS_NAME_MAX);
        if (!globals_t_p->fslist[i]) {
            fprintf(stderr, "memory allocation failed: %s:%d:%s\n", 
                __FILE__, __LINE__, __func__);
            exit(EXIT_FAILURE);       
        }
    }
    globals_t_p->fslist[0] = "ext4";
    globals_t_p->fslist[1] = "jffs2";
}

void free_all_globals() 
{
    for (int i = 0; i < globals_t_p->_n_fs; ++i)
        free(globals_t_p->fslist[i]);
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

void __attribute__((constructor)) globals_init()
{
    init_all_globals();
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) globals_cleanup()
{
    free_all_globals();
}
