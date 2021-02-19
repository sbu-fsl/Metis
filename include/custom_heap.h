#ifndef _CUSTOM_HEAP_H
#define _CUSTOM_HEAP_H

#include <stddef.h>

void try_init_myheap(void);
void *my_morecore(ptrdiff_t increment);
void unset_myheap(void);

#endif
