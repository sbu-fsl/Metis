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
#include "cr.h"
#include "nanotiming.h"
#include "vector.h"

static int seq = 0;

static struct timespec begin_ts;
static struct timespec last_ts;
static size_t last_seq;
static const int perf_interval = 5;

void perfstat(void) {
	struct timespec now, diff;
	current_utc_time(&now);
	timediff(&diff, &now, &last_ts);
	if (diff.tv_sec < perf_interval)
		return;

	struct timespec epoch;
	timediff(&epoch, &now, &begin_ts);
	// does not count checkpoint/restore
	size_t nops = seq - last_seq;
	double interval = diff.tv_sec + diff.tv_nsec * 1e-9;
	double rate = 1.0 * nops / interval;
	fprintf(stderr, "%ld.%09ld,%.3f\n", epoch.tv_sec, epoch.tv_nsec, rate);

	last_seq = seq;
	last_ts = now;
}

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
	/* This is to make sure data written to all file systems in the same
	 * group of operations is the same */
	int integer_to_write = seq / N_FS;
	generate_data(buffer, writelen, integer_to_write);
	int ret = write_file(filepath, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, offset, writelen, ret, errnoname(err));
	free(buffer);
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
void replayer_init()
{
	srand(time(0));
	for (int i = 0; i < N_FS; ++i) {
		size_t len = snprintf(NULL, 0, "/mnt/test-%s", fslist[i]);
		basepaths[i] = calloc(1, len + 1);
		snprintf(basepaths[i], len + 1, "/mnt/test-%s", fslist[i]);
	}
	current_utc_time(&begin_ts);
}

static size_t state_depth = 0;

static void do_checkpoint(const char *mp, size_t id)
{
	int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
	assert(mpfd >= 0);

	int res = ioctl(mpfd, VERIFS_CHECKPOINT, id);
	assert(res == 0);

	close(mpfd);
}

void checkpoint()
{
	state_depth++;
	printf("checkpoint (%zu)\n", state_depth);
	for (int i = 0; i < N_FS; ++i) {
		do_checkpoint(basepaths[i], state_depth);
	}
}

static void do_restore(const char *mp, size_t id)
{
	int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
	assert(mpfd >= 0);

	int res = ioctl(mpfd, VERIFS_RESTORE, id);
	assert(res == 0);

	close(mpfd);
}

void restore()
{
	printf("restore (%zu)\n", state_depth);
	for (int i = 0; i < N_FS; ++i) {
		do_restore(basepaths[i], state_depth);
	}
	state_depth--;
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
	replayer_init();
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d ", seq);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);
		bool flag_ckpt = false, flag_restore = false;
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
		} else if (strncmp(funcname, "checkpoint", len) == 0) {
			flag_ckpt = true;
			seq--;
		} else if (strncmp(funcname, "restore", len) == 0) {
			flag_restore = true;
			seq--;
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		seq++;
		if (flag_ckpt)
			checkpoint();
		if (flag_restore)
			restore();
		errno = 0;
		free(line);
		destroy_fields(&argvec);
		perfstat();
	}
	fclose(seqfp);
	free(linebuf);

	return 0;
}
