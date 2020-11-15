#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>

#define __USE_XOPEN_EXTENDED 1
#include <ftw.h>

#include "errnoname.h"
#include "fileutil.h"
#include "operations.h"
#include "vector.h"

int seq = 0;

void extract_fields(vector_t *fields_vec, char *line, const char *delim)
{
	vector_init(fields_vec, char *);
	char *field = strtok(line, delim);
	while (field) {
		size_t flen = strlen(field);
		char *field_copy = malloc(flen + 1);
		assert(field_copy);
		field_copy[flen] = '\0';
		strncpy(field_copy, field, flen);
		vector_add(fields_vec, &field_copy);
		field = strtok(NULL, ", ");
	}
}

void destroy_fields(vector_t *fields_vec)
{
	char **field;
	vector_iter(fields_vec, char *, field) {
		free(*field);
	}
	vector_destroy(fields_vec);
}

int do_create_file(vector_t *argvec)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *modestr = *vector_get(argvec, char *, 2);
	char *endptr;
	int mode = (int)strtol(modestr, &endptr, 8);
	int res = create_file(filepath, mode);
	printf("create_file(%s, 0%o) -> ret=%d, errno=%s\n",
	       filepath, mode, res, errnoname(errno));
	return res;
}

int do_write_file(vector_t *argvec)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *offset_str = *vector_get(argvec, char *, 3);
	char *len_str = *vector_get(argvec, char *, 4);
	char *endp;
	off_t offset = strtol(offset_str, &endp, 10);
	size_t writelen = strtoul(len_str, &endp, 10);
	assert(offset != LONG_MAX);
	assert(writelen != ULONG_MAX);
	
	char *buffer = malloc(writelen);
	assert(buffer != NULL);
	generate_data(buffer, writelen, -1);
	int ret = write_file(filepath, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, offset, writelen, ret, errnoname(err));
	return ret;
}

int do_truncate(vector_t *argvec)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *len_str = *vector_get(argvec, char *, 2);
	off_t flen = atol(len_str);
	
	int ret = truncate(filepath, flen);
	int err = errno;
	printf("truncate(%s, %ld) -> ret=%d, errno=%s\n",
	       filepath, flen, ret, errnoname(err));
	return ret;
}

int do_unlink(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = unlink(path);
	int err = errno;
	printf("unlink(%s) -> ret=%d, errno=%s\n",
	       path, ret, errnoname(err));
	return ret;
}

int do_mkdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	char *modestr = *vector_get(argvec, char *, 2);
	char *endp;
	int mode = (int)strtol(modestr, &endp, 8);
	int ret = mkdir(path, mode);
	int err = errno;
	printf("mkdir(%s, 0%o) -> ret=%d, errno=%s\n",
	       path, mode, ret, errnoname(err));
	return ret;
}

int do_rmdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = rmdir(path);
	int err = errno;
	printf("rmdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, errnoname(err));
	return ret;
}

/* Now I would expect the setup script to setup file systems instead. */
void init()
{
	srand(time(0));
}

void checkpoint(const char *devpath, char *buffer, size_t size)
{
	int devfd = open(devpath, O_RDONLY);
	assert(devfd >= 0);
	char *ptr = buffer;
	size_t remaining = size;
	const size_t bs = 4096;

	while (remaining > 0) {
		size_t readsz = (remaining > bs) ? bs : remaining;
		ssize_t res = read(devfd, ptr, readsz);
		assert(res >= 0);
		ptr += res;
		remaining -= res;
	}

	close(devfd);
}

void restore(const char *devpath, char *buffer, size_t size)
{
	int devfd = open(devpath, O_WRONLY);
	assert(devfd >= 0);
	char *ptr = buffer;
	size_t remaining = size;
	const size_t bs = 4096;

	while (remaining > 0) {
		size_t writesz = (remaining > bs) ? bs : remaining;
		ssize_t res = write(devfd, ptr, writesz);
		assert(res >= 0);
		ptr += res;
		remaining -= res;
	}

	close(devfd);
}

static float prob_ckpt = 0.1;
static float prob_restore = 0.1;

void ckpt_or_restore(const char *devpath, char *buffer, size_t size)
{
	static bool has_ckpt = false;
	int rnd = rand();
	float prob = 1.0 * rnd / RAND_MAX;

	if (prob <= prob_ckpt) {
		checkpoint(devpath, buffer, size);
		has_ckpt = true;
	} else if (prob >= (1.0 - prob_restore) && has_ckpt) {
		restore(devpath, buffer, size);
	}
}

int main(int argc, char **argv)
{
	FILE *seqfp = fopen("sequence.log", "r");
	ssize_t len;
	size_t linecap = 0;
	char *linebuf = NULL;
	if (!seqfp) {
		printf("Cannot open sequence.log. Does it exist?\n");
		exit(1);
	}
	init();
	/* probability of checkpoint and restore */
	/*
	if (argc >= 2) {
		int p1 = atoi(argv[1]);
		if (p1 > 0)
			prob_ckpt = 1.0 * p1 / 100;
		printf("Prob. of checkpoint is %d %%.\n", p1);
	}
	if (argc >= 3) {
		int p2 = atoi(argv[2]);
		if (p2 > 0)
			prob_restore = 1.0 * p2 / 100;
		printf("Prob. of restore is %d %%.\n", p2);
	}
	*/
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d ", seq++);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
			do_write_file(&argvec);
		} else if (strncmp(funcname, "truncate", len) == 0) {
			do_truncate(&argvec);
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(&argvec);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(&argvec);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(&argvec);
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		errno = 0;
		free(line);
		destroy_fields(&argvec);
		// assert(do_fsck());
		// ckpt_or_restore(devpath, fsimg, devsize);
	}
	fclose(seqfp);
	free(linebuf);

	return 0;
}
