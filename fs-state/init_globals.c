#include "init_globals.h"

globals_t *globals_t_p;

void init_all_globals() {
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p) {
        mem_alloc_err();
        exit(EXIT_FAILURE);
    }
    // _n_fs
    globals_t_p->_n_fs = 2;

    // fslist
    static const char *fslist_to_copy[] = {"ext4", "jffs2"};
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
}

void free_all_globals() 
{
    for (int i = 0; i < globals_t_p->_n_fs; ++i) {
        free(globals_t_p->fslist[i]);
    }
    free(globals_t_p->fslist);
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
