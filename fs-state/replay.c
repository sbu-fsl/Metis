#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/types.h>

#include "errnoname.h"
#include "fileutil.h"

int curfd = -1;
int opened_files[1024];
int _n_files = 0;
int seq = 0;

char *nextfield(char *base, char delim)
{
	char *res;
	if (!base || *base == '\0')
		return NULL;

	for (res = base; *res != delim; ++res);
	*res++ = '\0';
	return res;
}

int do_open(char *argstr)
{
	char *filepath = argstr;
	char *flagstr = nextfield(filepath, ':');
	char *modestr = nextfield(flagstr, ':');
	assert(filepath && flagstr && modestr);

	int openflag = atoi(flagstr), mode = atoi(modestr), fd, err;
	fd = open(filepath, openflag, mode);
	err = errno;
	printf("open(%s, %x, 0%o) -> fd=%d, errno=%s\n",
	       filepath, openflag, mode, fd, errnoname(err));
	if (fd >= 0) {
		curfd = fd;
		opened_files[_n_files] = fd;
		_n_files++;
	}
	return fd;
}

int do_lseek(char *argstr)
{
	char *offset_str = argstr;
	char *flag_str = nextfield(offset_str, ':');
	assert(offset_str && flag_str);

	off_t offset = atol(offset_str);
	int flag = atoi(flag_str);
	int ret = lseek(curfd, offset, flag);
	int err = errno;
	printf("lseek(%d, %ld, %d) -> ret=%d, errno=%s\n",
	       curfd, offset, flag, ret, errnoname(err));
	return ret;
}

int do_write(char *argstr)
{
	char *endp;
	size_t writelen = strtoul(argstr, &endp, 10);
	assert(writelen != ULONG_MAX);
	
	char *buffer = malloc(writelen);
	assert(buffer != NULL);
	generate_data(buffer, writelen, -1);
	int ret = write(curfd, buffer, writelen);
	int err = errno;
	printf("write(%d, %p, %lu) -> ret=%d, errno=%s\n",
	       curfd, buffer, writelen, ret, errnoname(err));
	return ret;
}

int do_ftruncate(char *argstr)
{
	off_t flen = atol(argstr);
	
	int ret = ftruncate(curfd, flen);
	int err = errno;
	printf("ftruncate(%d, %ld) -> ret=%d, errno=%s\n",
	       curfd, flen, ret, errnoname(err));
	return ret;
}

void do_closeall(void)
{
	for (int i = 0; i < _n_files; ++i) {
		close(opened_files[i]);
	}
	_n_files = 0;
	printf("closeall()\n");
}

int do_unlink(const char *path)
{
	int ret = unlink(path);
	int err = errno;
	printf("unlink(%s) -> ret=%d, errno=%s\n",
	       path, ret, errnoname(err));
	return ret;
}

int do_mkdir(const char *path)
{
	int ret = mkdir(path, 0755);
	int err = errno;
	printf("mkdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, errnoname(err));
	return ret;
}

int do_rmdir(const char *path)
{
	int ret = rmdir(path);
	int err = errno;
	printf("rmdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, errnoname(err));
	return ret;
}

void init()
{
	srand(time(0));
	system("dd if=/dev/zero of=/dev/ram0 bs=1k count=256");
	system("mkfs.ext4 -F /dev/ram0");
	system("mount -t ext4 -o rw,sync,noatime /dev/ram0 /mnt/test-ext4");
	system("rmdir /mnt/test-ext4/lost+found");
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

void ckpt_or_restore(const char *devpath, char *buffer, size_t size)
{
	const float prob_ckpt = 0.1;
	const float prob_restore = 0.1;
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
	const char *devpath = "/dev/ram0";
	const size_t devsize = 256 * 1024;
	FILE *seqfp = fopen("sequence.log", "r");
	size_t len, linecap = 0;
	char *linebuf = NULL;
	char *fsimg = malloc(devsize);
	if (!seqfp) {
		printf("Cannot open sequence.log. Does it exist?\n");
		exit(1);
	}
	init();
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d ", seq++);
		/* break func name and args by ':' */
		char *funcname = line;
		char *argstr = nextfield(line, ':');
		if (strncmp(funcname, "open", len) == 0) {
			do_open(argstr);
		} else if (strncmp(funcname, "lseek", len) == 0) {
			do_lseek(argstr);
		} else if (strncmp(funcname, "write", len) == 0) {
			do_write(argstr);
		} else if (strncmp(funcname, "ftruncate", len) == 0) {
			do_ftruncate(argstr);
		} else if (strncmp(funcname, "closeall", len) == 0) {
			do_closeall();
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(argstr);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(argstr);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(argstr);
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		errno = 0;
		free(line);
		ckpt_or_restore(devpath, fsimg, devsize);
	}
	fclose(seqfp);
	free(linebuf);

	return 0;
}
