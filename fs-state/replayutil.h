#ifndef _REPLAY_H_
#define _REPLAY_H_

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>

#define __USE_XOPEN_EXTENDED 1
#include <ftw.h>

#include "vector.h"

#include "errnoname.h"
#include "fileutil.h"
#include "operations.h"

typedef struct concrete_state {
	int seqid;
	char **images;
} fs_state_t;

void extract_fields(vector_t *fields_vec, char *line, const char *delim);
void destroy_fields(vector_t *fields_vec);
int do_create_file(vector_t *argvec);
int do_write_file(vector_t *argvec, int seq);
int do_truncate(vector_t *argvec);
int do_unlink(vector_t *argvec);
int do_mkdir(vector_t *argvec);
int do_rmdir(vector_t *argvec);
int do_rename(vector_t *argvec);
int do_symlink(vector_t *argvec);
int do_link(vector_t *argvec);
void replayer_init(vector_t states);
void checkpoint(int seq, vector_t states);
void restore(vector_t states);

#endif
