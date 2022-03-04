#include "init_globals.h"

globals_t *globals_t_p;

void init_all_globals() {
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p) {
        fprintf(stderr, "Memory allocation failed: %s:%d:%s\n", 
            __FILE__, __LINE__, __func__);
        exit(EXIT_FAILURE);
    }
    globals_t_p->_n_fs = 2;
}

void free_all_globals() {
    free(globals_t_p);
}

unsigned int get_n_fs()
{
    return globals_t_p->_n_fs;
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
