#ifndef _INIT_GLOBALS_H_
#define _INIT_GLOBALS_H_

#include <stdio.h>
#include <stdlib.h>
#include "abstract_fs.h"
#include "whichconfig.h"

extern globals_t *globals_t_p;

void init_all_globals();
void free_all_globals();

unsigned int get_n_fs();

#endif
