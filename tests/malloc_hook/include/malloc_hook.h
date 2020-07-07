#ifndef _MALLOC_HOOK_H_
#define _MALLOC_HOOK_H_

#include "my_malloc.h"

/* Prototypes for our hooks.  */
void my_init (void);
void *my_malloc_hook (size_t, const void *);
void my_free_hook (void*, const void *);

#endif