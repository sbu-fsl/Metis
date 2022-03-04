#include "init_globals.h"

globals_t *globals_t_p;

void init_all_globals() {
    globals_t_p = malloc(sizeof(globals_t));
    if (!globals_t_p) {
        fprintf(stderr, "cannot allocate memory for global structure\n");
        exit(EXIT_FAILURE);
    }
    printf("init_all_globals malloc globals_t_p value: %p\n", globals_t_p);
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
    printf("init_all_globals globals_t_p value: %p\n", globals_t_p);
    printf("init_all_globals get_n_fs value: %d\n", get_n_fs());
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) globals_cleanup()
{
    free_all_globals();
}
