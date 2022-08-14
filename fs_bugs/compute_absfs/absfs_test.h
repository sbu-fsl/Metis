#include "abstract_fs.h"
#include <stdio.h>
#include <stdlib.h>

#ifndef _ABSFS_TEST_H
#define _ABSFS_TEST_H

char *get_abstract_state(const char *basepath, unsigned int hash_method, char *abs_state_str);

#endif // _ABSFS_TEST_H
