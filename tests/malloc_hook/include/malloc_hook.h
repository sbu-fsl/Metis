#ifndef _MALLOC_HOOK_H_
#define _MALLOC_HOOK_H_

#include "my_malloc.h"

/* Prototypes for our hooks.  */
<<<<<<< HEAD
void my_init (void);
=======
void my_init_hook (void);
>>>>>>> a61a9f0bf2787bdd30bb38e23f2f6a870a2b43fb
void *my_malloc_hook (size_t, const void *);
void my_free_hook (void*, const void *);

#endif