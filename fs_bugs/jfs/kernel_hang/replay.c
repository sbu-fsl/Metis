/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Divyaank Tiwari
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ftw.h>
#include <assert.h>
#include <stdint.h>
#include <stdarg.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/ioctl.h>
#include <sys/xattr.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <openssl/md5.h>
#include <stddef.h>
#include <sys/types.h>
#include <math.h>
#include <limits.h>
#include <openssl/opensslv.h>

//From operations.h
/* Max length of function name in log */
#define FUNC_NAME_LEN    16

//From vector.h
#define DEFAULT_INITCAP 16

#ifndef PATH_MAX
#define PATH_MAX    4096
#endif

int pre = 0;
int seq = 0;
unsigned int n_fs = 1;
char *fsys = "jfs";
char *fssuffix = "-i1-s0";
char *device = "/dev/ram1";
size_t devsize = (size_t)16384;
char *basepath = "/mnt/test-jfs-i1-s0";

struct vector {
    unsigned char *data;
    size_t unitsize;
    size_t len;
    size_t capacity;
};

typedef struct vector vector_t;

static inline void _vector_init(struct vector *vec, size_t unitsize, size_t initcap) {
    if (initcap < DEFAULT_INITCAP)
        initcap = DEFAULT_INITCAP;
    vec->unitsize = unitsize;
    vec->len = 0;
    vec->capacity = initcap;
    vec->data = (unsigned char *)calloc(initcap, unitsize);
}
#define vector_init_2(vec, type)    _vector_init(vec, sizeof(type), DEFAULT_INITCAP)
#define vector_init_3(vec, type, initcap)   _vector_init(vec, sizeof(type), initcap)
#define vector_init_x(a, b, c, func, ...)   func
/* Macro function with optional arg: vector_init(struct vector *vec, type, [initcap=16]) */
#define vector_init(...)    vector_init_x(__VA_ARGS__,\
                                          vector_init_3(__VA_ARGS__),\
                                          vector_init_2(__VA_ARGS__)\
                                         )

static inline int vector_expand(struct vector *vec) {
    size_t newcap = vec->unitsize * vec->capacity * 2;
    unsigned char *newptr = (unsigned char *)realloc(vec->data, newcap);
    if (newptr == NULL)
        return ENOMEM;
    vec->data = newptr;
    vec->capacity *= 2;
    return 0;
}

static inline int vector_add(struct vector *vec, void *el) {
    int ret;
    if (vec->len >= vec->capacity) {
        if ((ret = vector_expand(vec)) != 0)
            return ret;
    }
    size_t offset = vec->len * vec->unitsize;
    memcpy(vec->data + offset, el, vec->unitsize);
    vec->len++;
    return 0;
}

static inline void *_vector_get(struct vector *vec, size_t index) {
    if (index < 0 || index >= vec->len)
        return NULL;
    return (void *)(vec->data + index * vec->unitsize);
}

#define vector_get(vec, type, index) \
    (type *)_vector_get(vec, index)

static inline void *_vector_peek_top(struct vector *vec) {
    if (vec->len == 0)
        return NULL;
    return (void *)(vec->data + (vec->len - 1) * vec->unitsize);
}

#define vector_peek_top(vec, type) \
    (type *)_vector_peek_top(vec)

static inline void vector_destroy(struct vector *vec) {
    free(vec->data);
    memset(vec, 0, sizeof(struct vector));
}

#define vector_iter(vec, type, entry) \
    int _i; \
    for (entry = (type *)((vec)->data), _i = 0; _i < (vec)->len; ++_i, ++entry)

extern char func[FUNC_NAME_LEN + 1];

#define min(x, y) ((x >= y) ? y : x)

enum fill_type {PATTERN, ONES, BYTE_REPEAT, RANDOM_EACH_BYTE};

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

/* Generate data into a given buffer.
 * @value: 0-255 for uniform characters, -1 for random filling */
static inline void generate_data(char *buffer, size_t len, size_t offset, enum fill_type type, int value)
{
    switch (type) {
    /* ONES: write all byte 1 */
    case ONES:
        memset(buffer, 1, len);
        break;
    /* BYTE_REPEAT: select a random byte but write this byte uniformly */
    case BYTE_REPEAT:
        memset(buffer, value, len);
        break;
    /* PATTERN: write the bytes that are the same as the value of offsets */
    case PATTERN:
    {
        int new_offset = 3 - offset % sizeof(int);
        for (int i = 0; i < new_offset; i++) {
            buffer[i] = 0;
        }
        int *ip = (int *) (buffer + new_offset);
        for (int i = 0; i <= len / sizeof(int); i++) {
            ip[i] = offset / sizeof(int) + i;
        }
        break;
    }
    /* RANDOM_EACH_BYTE: write random value for each int size (4 bytes) */
    case RANDOM_EACH_BYTE:
    {
        size_t i = 0, remaining = len;
        int n = rand();
        while (remaining > 0) {
            int *ptr = (int *)(buffer + i);
            *ptr = n;
            remaining -= min(sizeof(int), remaining);
            i += min(sizeof(int), remaining);
        }
        break;
    }
    }
}

static inline ssize_t fsize(int fd)
{
    struct stat info;
    int ret = fstat(fd, &info);
    if (ret != 0)
        return -1;
    if (info.st_mode & S_IFREG) {
        // verify st_size is even multiple of 4096
        const size_t bs = 4096;
        if (info.st_size % bs != 0)
            return -1;
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return -1;
        return devsz;
    } else {
        return -1;
    }
}

void unmount_all(bool strict);

static inline void unmount_all_strict()
{
    unmount_all(true);
}

static inline void unmount_all_relaxed()
{
    unmount_all(false);
}

int create_file(const char *path, int flags, int mode)
{
    int fd = open(path, flags, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, int flags, void *data, off_t offset, size_t length)
{
    int fd = open(path, flags, O_RDWR);
    int err;
    if (fd < 0) {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit_err;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
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
	       filepath, flags, mode, res, strerror(errno));
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
	int integer_to_write = seq / n_fs;
	generate_data(buffer, writelen, offset, BYTE_REPEAT, integer_to_write);
	int ret = write_file(filepath, flags, buffer, offset, writelen);
	int err = errno;
	printf("write_file(%s, %o, %ld, %lu) -> ret=%d, errno=%s\n",
	       filepath, flags, offset, writelen, ret, strerror(err));
	free(buffer);
	return ret;
}

int do_unlink(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = unlink(path);
	int err = errno;
	printf("unlink(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
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
	       path, mode, ret, strerror(err));
	return ret;
}

int do_rmdir(vector_t *argvec)
{
	char *path = *vector_get(argvec, char *, 1);
	int ret = rmdir(path);
	int err = errno;
	printf("rmdir(%s) -> ret=%d, errno=%s\n",
	       path, ret, strerror(err));
	return ret;
}

void mountall()
{
    int failpos, err;

    int ret = -1;
    ret = mount(device, basepath, fsys, MS_NOATIME, "");     
    if (ret != 0) {
        // failpos = i;
        err = errno;
        goto err;
    }

    return;
err:
    /* undo mounts */
    for (int i = 0; i < failpos; ++i) {
        umount2(basepath, MNT_FORCE);
    }
    fprintf(stderr, "Could not mount file system %s in %s at %s (%s)\n",
            fsys, device, basepath,
            strerror(err));
    exit(1);
}

void unmount_all(bool strict)
{
    bool has_failure = false;
    int ret;

    // Change retry limit from 20 to 19 to avoid excessive delay
    int retry_limit = 19;
    int num_retries = 0;
    
    while (retry_limit > 0) {
        ret = umount2(basepath, 0);
        if (ret == 0) {
            break; // Success, exit the retry loop
        }        

        /* If unmounting failed due to device being busy, again up to
        * retry_limit times with 100 * 2^n ms (n = num_retries) */
        if (errno == EBUSY) {
            // 100 * (1 <<  0) = 100ms
            // 100 * (1 << 18) = 100 * 262144 = 26.2144s
            useconds_t waitms = 100 * (1 << num_retries); // Exponential backoff starting at 100ms
            fprintf(stderr, "File system %s mounted on %s is busy. Retry %d times,"
                    "unmounting after %dms.\n", fsys, basepath, num_retries + 1,
                    waitms);
            usleep(1000 * waitms);
            num_retries++;
            retry_limit--;
        } 
        else {
            // Handle non-EBUSY errors immediately without retrying
            fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                    fsys, basepath, strerror(errno));
            has_failure = true;
        }
    }
    
    if (retry_limit == 0) {
        fprintf(stderr, "Failed to unmount file system %s at %s after retries.\n",
                fsys, basepath);
        has_failure = true;
    }
    if (has_failure && strict)
        exit(1);
}


static void execute_cmd(const char *cmd)
{
    int retval = system(cmd);
    int status, signal = 0;
    if ((status = WEXITSTATUS(retval)) != 0) {
        fprintf(stderr, "Command `%s` failed with %d.\n", cmd, status);
    }
    if (WIFSIGNALED(retval)) {
        signal = WTERMSIG(retval);
        fprintf(stderr, "Command `%s` terminated with signal %d.\n", cmd,
                signal);
    }
    if (status || signal) {
        exit(1);
    }
}

static int check_device(const char *devname, const size_t exp_size_kb)
{
    int fd = open(devname, O_RDONLY);
    struct stat devinfo;
    if (fd < 0) {
        fprintf(stderr, "Cannot open %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        return -errno;
    }
    int retval = fstat(fd, &devinfo);
    if (retval < 0) {
        fprintf(stderr, "Cannot stat %s (err=%s, %d)\n",
                devname, strerror(errno), errno);
        close(fd);
        return -errno;
    }
    if (!S_ISBLK(devinfo.st_mode)) {
        fprintf(stderr, "%s is not a block device.\n", devname);
        close(fd);
        return -ENOTBLK;
    }
    size_t devsize = fsize(fd);
    if (devsize < exp_size_kb * 1024) {
        fprintf(stderr, "%s is smaller than expected (expected %zu KB, "
                "got %zu).\n", devname, exp_size_kb, devsize / 1024);
        close(fd);
        return -ENOSPC;
    }
    close(fd);
    return 0; 
}

static void populate_mountpoints()
{
    char check_mount_cmdbuf[PATH_MAX];
    char unmount_cmdbuf[PATH_MAX];
    char check_mp_exist_cmdbuf[PATH_MAX];
    char rm_mp_cmdbuf[PATH_MAX];
    char mk_mp_cmdbuf[PATH_MAX];

    snprintf(check_mount_cmdbuf, PATH_MAX, "mount | grep %s", basepath);    
        /* If the mountpoint has fs mounted, then unmount it */
    
    int check_mount_cmdbuf_retval = system(check_mount_cmdbuf);
    int check_mount_cmdbuf_status = WEXITSTATUS(check_mount_cmdbuf_retval);

    if (check_mount_cmdbuf_status == 0) {
        snprintf(unmount_cmdbuf, PATH_MAX, "umount -f %s", basepath);
        execute_cmd(unmount_cmdbuf);
    }
    /* 
     * Caveat: if we use file/dir pools and test in-memory file systems
     * like VeriFS, we should not remove the mount point here because
     * we need to pre-create files/dirs in the pool. Removing mountpoints
     * simply erase the precreated files/dirs.
     *
     * Also, we cannot mount VeriFS and other in-memory file systems on
     * a non-empty mount point.
     * 
     * The correct way would be removing and recreating mount point of 
     * VeriFS in the setup shell scripts before running pan.
     */

    snprintf(mk_mp_cmdbuf, PATH_MAX, "mkdir -p %s", basepath);
    execute_cmd(mk_mp_cmdbuf);
}

static int setup_jfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.jfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

void setup_filesystems()
{
    int ret;
    populate_mountpoints();

    if (strcmp(fsys, "jfs") == 0) {
		ret = setup_jfs(device, devsize());
    } 
    
    if (ret != 0)
    {
        fprintf(stderr, "Cannot setup %s file system (ret = %d)\n", fsys, ret);
        exit(1);
    }
}

int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode)
{
    const size_t len = strlen(path);
    char _path[PATH_MAX];
    char *p; 

    errno = 0;

    /* Copy string so its mutable */
    if (len > sizeof(_path)-1) {
        errno = ENAMETOOLONG;
        return -1; 
    }   
    strcpy(_path, path);

    bool next_f = false;
    bool next_d = false;
    /* Iterate the string */
    for (p = _path + 1; *p; p++) {
        if (*p == '/') {
            /* Temporarily truncate */
            *p = '\0';
            if (mkdir(_path, dir_mode) != 0) {
                if (errno != EEXIST) {
                    return -1; 
                }
            }
            
            *p = '/';

            if (*(p + 1) == 'f')
                next_f = true;
            else if (*(p + 1) == 'd')
                next_d = true;
        }
    }
    if (next_f) {
        int fd = creat(_path, file_mode);
        if (fd >= 0) {
            close(fd);
        }
        else if (errno != EEXIST) {
            return -1;
        }
    }
    if (next_d) {
        if (mkdir(_path, dir_mode) != 0) {
            if (errno != EEXIST) {
                return -1; 
            }
        }
    }

    return 0;
}

/* 
 * NOTE: NEED TO RECOMPILE REPLAYER "make replayer" every time we run it.
 *
 * Make sure the required devices are already set up with correct sizes. 
 *
 * Before running this program, make sure the devices are already set 
 * up with correct sizes.
 * We need to specify a sequence.log file (the sequence of operations 
 * to be replayed)
 * and a dump_prepopulate_*.log file (precreated files and dirs).
 * Usage: 
 *		sudo ./replay -K 0:ext4:256:jfs:16384 2>&1 > replay_jfs.log
 *		sudo ./replay -K 0:ext4:256:nilfs2:1028
 *		sudo ./replay -K 0:nilfs2:1028
 */
int main(int argc, char **argv)
{
	/* 
	 * Open the dump_prepopulate_*.log files to create the pre-populated
	 * files and directories.
	 */
	char *dump_prepopulate_file_name = "dump_prepopulate_0_kh6.log";
    char *sequence_log_file_name = "jfs_op_sequence.log";

    FILE *pre_fp = fopen(dump_prepopulate_file_name, "r");
	
	if (!pre_fp) {
		printf("Cannot open %s. Does it exist?\n", dump_prepopulate_file_name);
		exit(1);
	}
	
	/* Open sequence file */
	FILE *seqfp = fopen(sequence_log_file_name, "r");
	
	if (!seqfp) {
		printf("Cannot open %s. Does it exist?\n", sequence_log_file_name);
		exit(1);
	}

	ssize_t len, pre_len;
	size_t linecap = 0, pre_linecap = 0;
	char *linebuf = NULL, *pre_linebuf = NULL;

	/* Populate mount points and mkfs the devices */
	setup_filesystems();
	/* Create the pre-populated files and directories */
	mountall();
	while ((pre_len = getline(&pre_linebuf, &pre_linecap, pre_fp)) >= 0) {
		char *line = malloc(pre_len + 1);
		line[pre_len] = '\0';
		strncpy(line, pre_linebuf, pre_len);
		/* remove the newline character */
		if (line[pre_len - 1] == '\n')
			line[pre_len - 1] = '\0';
		printf("pre=%d \n", pre);
		/* parse the line for pre-populated files and directories */
		size_t pre_path_len;
		char *pre_path_name;
		
		pre_path_len = snprintf(NULL, 0, "%s%s", basepath, line);
		pre_path_name = calloc(1, pre_path_len + 1);
		snprintf(pre_path_name, pre_path_len + 1, "%s%s", basepath, line);
		// printf("pre_path_name=%s\n", pre_path_name);
		int ret = -1;
		ret = mkdir_p(pre_path_name, 0755, 0644);
		if (ret < 0) {
			fprintf(stderr, "mkdir_p error happened!\n");
			exit(EXIT_FAILURE);
		}
		free(pre_path_name);
		
		pre++;
	}
	unmount_all_strict();
	/* Replay the actual operation sequence */
	while ((len = getline(&linebuf, &linecap, seqfp)) >= 0) {
		char *line = malloc(len + 1);
		line[len] = '\0';
		strncpy(line, linebuf, len);
		/* remove the newline character */
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		printf("seq=%d \n", seq);
		/* parse the line */
		vector_t argvec;
		extract_fields(&argvec, line, ", ");
		char *funcname = *vector_get(&argvec, char *, 0);

		mountall();
		
		if (strncmp(funcname, "create_file", len) == 0) {
			do_create_file(&argvec);
		} else if (strncmp(funcname, "write_file", len) == 0) {
			do_write_file(&argvec, seq);
		} else if (strncmp(funcname, "unlink", len) == 0) {
			do_unlink(&argvec);
		} else if (strncmp(funcname, "mkdir", len) == 0) {
			do_mkdir(&argvec);
		} else if (strncmp(funcname, "rmdir", len) == 0) {
			do_rmdir(&argvec);
		} else {
			printf("Unrecognized op: %s\n", funcname);
		}
		
		seq++;

		unmount_all_strict();
		errno = 0;
		free(line);
		destroy_fields(&argvec);
	}
	/* Clean up */
	fclose(pre_fp);
	fclose(seqfp);
	free(pre_linebuf);
	free(linebuf);

	return 0;
}