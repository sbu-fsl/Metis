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
#include <linux/loop.h>
#include <string.h>

#include "errnoname.h"
#include "fileutil.h"
#include "operations.h"
#include "vector.h"

int seq = 0;

int fds[2][3];

typedef struct concrete_state {
	int seqid;
	char **images;
} fs_state_t;

vector_t states;

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
	for (int i = 0; i < get_n_fs(); ++i) {
		do_checkpoint(get_loopdevlist()[i], &state.images[i]);
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

void restore()
{
	fs_state_t *state = vector_peek_top(&states, fs_state_t);
	if (!state)
		return;
	for (int i = 0; i < get_n_fs(); ++i) {
		do_restore(get_devlist_replayer()[i], state->images[i]);
	}
	if (state->images)
		free(state->images);
	vector_pop_back(&states);
	printf("restore (to the state just before seqid = %d)\n", state->seqid);
}

void associate_loop_devs(){
	int err;
	for (int i = 0; i < get_n_fs(); ++i) {
		//create loop device and mount.
		//open fs img
		fds[i][0] = openat(AT_FDCWD, get_devlist_replayer()[i], O_RDWR|O_CLOEXEC);
		if( fds[i][0] == -1 ){
			err = errno;
			printf("Could not open fsimg %s.\n", get_devlist_replayer()[i]);
			goto err;
		}

		//open loop dev
		fds[i][1] = openat(AT_FDCWD, get_loopdevlist()[i], O_RDWR|O_CLOEXEC);
		if( fds[i][1] == -1 ){
			err = errno;
			printf("Could not open loop device %s.\n", get_loopdevlist()[i]);
			goto err;
		}

		//associate loop dev to fs img.
		fds[i][2]  = ioctl(fds[i][1], LOOP_SET_FD, fds[i][0]);
		if ( fds[i][2] == -1 ) {
			err = errno;
			printf("Could not associate fsimg %s to loop device %s .\n", get_devlist_replayer()[i], get_loopdevlist()[i]);
			goto err;
		}
		printf("Associated loop dev %s to fs img %s\n", get_loopdevlist()[i], get_devlist_replayer()[i]);
	}

	for (int i = 0; i < get_n_fs(); ++i) {
		for(int j = 0; j < 2; j++ ){
			if( close(fds[i][j]) == -1 ) {
				err = errno;
				goto err;
			}
		}
	}
	return;
err:
	printf("Could not associate/mount loop device, errno %s", errnoname(errno));		
	exit(1);
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

	//reading the file from end to find out first "taking_snapshot"
	if( argc == 4 && strcmp(argv[3], "-c") == 0 ){
		fseek(seqfp, 0, SEEK_END);
		int count = 0;
		while (ftell(seqfp) > 1 ){
			fseek(seqfp, -2, SEEK_CUR);
			if(ftell(seqfp) <= 2)
				break;
			char ch =fgetc(seqfp);
			count = 0;
			char line[400] = "";
			while(ch != '\n'){
				line[count++] = ch;
				if(ftell(seqfp) < 2)
					break;
				fseek(seqfp, -2, SEEK_CUR);
				ch = fgetc(seqfp);
			}
			//TODO: Reverse the string and compare.
			if(strcmp(line, "tohspans_gnikat") == 0){
				//going to next line
				while(fgetc(seqfp) != '\n'){

				}
				break;
			}
			long offset = ftell(seqfp);
			fseek ( seqfp , offset , SEEK_SET );
		}
	}

	replayer_init();

	if( argc == 4 && strcmp(argv[3],"-c") == 0 ){
		associate_loop_devs();
	}

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
		
		if( argc == 4 && strcmp(argv[3],"-c") == 0 ){
			//mounting the fs image -- need to skip verifs?
			mount_fs_images();
		}
		else{
			mountall();
		}


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
