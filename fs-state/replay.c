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

#define DUMP_REPLAY_IMAGES 1

// The seq number to dump images (dump images only if seqid greater or equal to this value)
#define SEQID_DUMP_THRESHOLD 17126800

int seq = 0;

typedef struct concrete_state {
	int seqid;
	char **images;
} fs_state_t;

vector_t states;

/* Replayer dump device utilities */
static size_t state_depth = 0;

static int ensure_dump_dir(const char *folder)
{
    struct stat st;
    int ret = stat(folder, &st);
    /* Try creating the folder if it doesn't exist */
    if (ret < 0 && errno == ENOENT) {
        ret = mkdir(folder, 0755);
        if (ret < 0) {
            fprintf(stderr, "[ERROR]: %s: cannot create folder %s (%s)\n", __func__,
                    folder, errnoname(errno));
            return -errno;
        }
    } else if (ret < 0) {
        fprintf(stderr, "[ERROR]: %s: failed to stat %s, error is %s\n", __func__,
                folder, errnoname(errno));
        return -errno;
    } else {
        if (!S_ISDIR(st.st_mode)) {
            errno = ENOTDIR;
            fprintf(stderr, "[ERROR]: %s: folder %s is not a directory.\n", __func__,
                    folder);
            return -ENOTDIR;
        }
    }
    return 0;
}


static void dump_replay_mmaped(const char *folder, int i, char *fs_img)
{
	char outpath[PATH_MAX] = {0};
	snprintf(outpath, PATH_MAX, "%s/%s-mmap-%d-%zu.img", folder,
            get_fslist()[i], seq, state_depth);
    const size_t bs = 4096;
    int dmpfd = open(outpath, O_CREAT | O_RDWR | O_TRUNC, 0666);
    if (dmpfd < 0) {
        fprintf(stderr, "[ERROR]: cannot create file %s", outpath);
        return;
    }

	int fsfd = open(get_devlist()[i], O_RDWR);
    size_t remaining = fsize(fsfd);
    char *ptr = fs_img;
    while (remaining > 0) {
        size_t writelen = (remaining >= bs) ? bs : remaining;
        ssize_t writeres = write(dmpfd, ptr, writelen);
        if (writeres < 0) {
            fprintf(stderr, "[ERROR]: cannot write data to image dump %s", outpath);
            close(dmpfd);
            break;
        }
        ptr += writeres;
        remaining -= writeres;
    }
    close(dmpfd);
	close(fsfd);
}

static void dump_replay_device(const char *folder, int i)
{
	char *devname = get_devlist()[i];
	char *fsname = get_fslist()[i];

    char cmd[ARG_MAX] = {0};
    snprintf(cmd, ARG_MAX, "dd if=%s of=%s/%s-dev-%d-%zu.img bs=4k status=none",
             devname, folder, fsname, seq, state_depth);
    int status = system(cmd);
    if (WIFEXITED(status)) {
        if (WEXITSTATUS(status) != 0) {
            fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd exited with %d.",
                    fsname, devname, WEXITSTATUS(status));
        }
    } else if (WIFSIGNALED(status)) {
        fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd was terminated by signal "
                "%d.", fsname, devname, WTERMSIG(status));
    } else {
        fprintf(stderr, "[ERROR]: Cannot dump %s on %s, dd has exit code %d.",
                fsname, devname, status);
    }
}

static void dump_replay_fs_images(const char *folder, char **fs_imgs)
{
    assert(ensure_dump_dir(folder) == 0);
    for (int i = 0; i < get_n_fs(); ++i) {
        /* Dump the mmap'ed object */
        dump_replay_mmaped(folder, i, fs_imgs[i]);
        /* Dump the device by direct copying */
        dump_replay_device(folder, i);
    }

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
	int integer_to_write = seq / get_n_fs();
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

void checkpoint()
{
	fs_state_t state;
	state.seqid = seq;
	state.images = calloc(get_n_fs(), sizeof(char *));

	printf("checkpoint (the state seqid = %d, state_depth = %zu)\n", seq, state_depth);
	state_depth++;

	for (int i = 0; i < get_n_fs(); ++i) {
		do_checkpoint(get_devlist()[i], &state.images[i]);
	}
	vector_add(&states, &state);

	// dump checkpoint image here
	if (seq >= SEQID_DUMP_THRESHOLD)
		dump_replay_fs_images("replay-before-checkpoint", state.images);
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

	munmap(ptr, size);
	close(devfd);
}

void restore()
{
	fs_state_t *state = vector_peek_top(&states, fs_state_t);
	if (!state)
		return;

	printf("restore (to the state just before seqid = %d, state_depth = %zu)\n", state->seqid, state_depth);
	state_depth--;

	for (int i = 0; i < get_n_fs(); ++i) {
		do_restore(get_devlist()[i], state->images[i]);
	}
	// dump restored image here
	if (seq >= SEQID_DUMP_THRESHOLD)
		dump_replay_fs_images("replay-after-restore", state->images);
	for (int i = 0; i < get_n_fs(); ++i) {
		if (state->images[i])
			free(state->images[i]);
	}
	if (state->images)
		free(state->images);
	vector_pop_back(&states);
}

int main(int argc, char **argv)
{
	FILE *seqfp = fopen("sequence-pan-20220522-182011-2443643.log", "r");
	ssize_t len;
	size_t linecap = 0;
	char *linebuf = NULL;
	if (!seqfp) {
		printf("Cannot open sequence.log. Does it exist?\n");
		exit(1);
	}
	replayer_init();
	setup_filesystems();
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
		mountall();
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
		unmount_all_strict();
		if (flag_ckpt)
			checkpoint();
		if (flag_restore)
			restore();
		errno = 0;
		free(line);
		destroy_fields(&argvec);
	}
	fclose(seqfp);
	free(linebuf);

	return 0;
}
