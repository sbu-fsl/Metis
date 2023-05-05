#include "replayutil.h"

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
	char *flagstr = *vector_get(argvec, char *, 2);
	char *modestr = *vector_get(argvec, char *, 3);
	char *endptr;
	int flags = (int)strtol(flagstr, &endptr, 8);
	int mode = (int)strtol(modestr, &endptr, 8);
	int res = create_file(filepath, flags, mode);
	printf("create_file(%s, 0%o, 0%o) -> ret=%d, errno=%s\n",
	       filepath, flags, mode, res, errnoname(errno));
	return res;
}

int do_write_file(vector_t *argvec, int seq)
{
	char *filepath = *vector_get(argvec, char *, 1);
	char *flagstr = *vector_get(argvec, char *, 2);
	char *offset_str = *vector_get(argvec, char *, 4);
	char *len_str = *vector_get(argvec, char *, 5);
	char *endp;
	int flags = (int)strtol(flagstr, &endp, 8);
	off_t offset = strtol(offset_str, &endp, 10);
	size_t writelen = strtoul(len_str, &endp, 10);
	assert(offset != LONG_MAX);
	assert(writelen != ULONG_MAX);
	
	char *buffer = malloc(writelen);
	assert(buffer != NULL);
	/* This is to make sure data written to all file systems in the same
	 * group of operations is the same */
	int integer_to_write = seq / get_n_fs();
	generate_data(buffer, writelen, offset, BYTE_REPEAT, integer_to_write);
	int ret = write_file(filepath, flags, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %o, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, flags, offset, writelen, ret, errnoname(err));
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
int do_rename(vector_t *argvec)
{
	char *srcpath = *vector_get(argvec, char *, 1);
	char *dstpath = *vector_get(argvec, char *, 2);

	int ret = rename(srcpath, dstpath);
	int err = errno;
	printf("rename(%s, %s) -> ret=%d, errno=%s\n",
	       srcpath, dstpath, ret, errnoname(err));
	return ret;
}
int do_symlink(vector_t *argvec)
{
	char *srcpath = *vector_get(argvec, char *, 1);
	char *dstpath = *vector_get(argvec, char *, 2);

	int ret = symlink(srcpath, dstpath);
	int err = errno;
	printf("symlink(%s, %s) -> ret=%d, errno=%s\n",
	       srcpath, dstpath, ret, errnoname(err));
	return ret;
}
int do_link(vector_t *argvec)
{
	char *srcpath = *vector_get(argvec, char *, 1);
	char *dstpath = *vector_get(argvec, char *, 2);

	int ret = link(srcpath, dstpath);
	int err = errno;
	printf("link(%s, %s) -> ret=%d, errno=%s\n",
	       srcpath, dstpath, ret, errnoname(err));
	return ret;
}


/* Now I would expect the setup script to setup file systems instead. */
void replayer_init(vector_t states)
{
	srand(time(0));
	for (int i = 0; i < get_n_fs(); ++i) {
		size_t len = snprintf(NULL, 0, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
		get_basepaths()[i] = calloc(1, len + 1);
		snprintf(get_basepaths()[i], len + 1, "/mnt/test-%s%s", 
								get_fslist()[i], get_fssuffix()[i]);
	}
	vector_init(&states, fs_state_t);
}

static void do_checkpoint(const char *devpath, char **bufptr)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t fs_size = fsize(devfd);
	char *buffer, *ptr;
	// size_t remaining = fs_size;
	// const size_t bs = 4096;

	ptr = mmap(NULL, fs_size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	buffer = malloc(fs_size);
	assert(buffer);

	memcpy(buffer, ptr, fs_size);
	*bufptr = buffer;

	munmap(ptr, fs_size);
	close(devfd);
}

void checkpoint(int seq, vector_t states)
{
	fs_state_t state;
	state.seqid = seq;
	state.images = calloc(get_n_fs(), sizeof(char *));
	for (int i = 0; i < get_n_fs(); ++i) {
		do_checkpoint(get_devlist()[i], &state.images[i]);
	}
	vector_add(&states, &state);
	printf("checkpoint\n");
}

static void do_restore(const char *devpath, char *buffer)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t size = fsize(devfd);
	char *ptr;

	ptr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	
	memcpy(ptr, buffer, size);
        free(buffer);

	munmap(ptr, size);
	close(devfd);
}

void restore(vector_t states)
{
	fs_state_t *state = vector_peek_top(&states, fs_state_t);
	if (!state)
		return;
	for (int i = 0; i < get_n_fs(); ++i) {
		do_restore(get_devlist()[i], state->images[i]);
	}
	if (state->images)
		free(state->images);
	vector_pop_back(&states);
	printf("restore (to the state just before seqid = %d)\n", state->seqid);
}
