#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <linux/limits.h>
#include <linux/fs.h>
#include <unistd.h>
#include <sys/vfs.h>

#include "abstract_fs.h"

#define MAX_FILES 10 
#define MAX_DIRS 10
#define ABSFS_LENGTH 33 // 16 * 2 + 1

static inline ssize_t fsize(int fd)
{
    struct stat info;
    int ret = fstat(fd, &info);
    if (ret != 0)
        return -1;
    if (info.st_mode & S_IFREG) {
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return 0;
        return devsz;
    } else {
        return 0;
    }
}

static void do_checkpoint(const char *devpath, char **bufptr)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t fs_size = fsize(devfd);
	char *buffer, *ptr;

	ptr = mmap(NULL, fs_size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	buffer = malloc(fs_size);
	assert(buffer);

	memcpy(buffer, ptr, fs_size);
	*bufptr = buffer;

	munmap(ptr, fs_size);
	close(devfd);
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

static char *get_abstract_state(const char *basepath,
    unsigned int hash_method, char *abs_state_str)
{
    int ret;
    absfs_t absfs;
    absfs.hash_option = hash_method;
    init_abstract_fs(&absfs);
    ret = scan_abstract_fs(&absfs, basepath, false, printf);

    if (ret) {
        printf("Error occurred when computing absfs...\n");
        return NULL;
    }

    char *strp = abs_state_str;
    for (int i = 0; i < 16; ++i) {
        size_t res = snprintf(strp, 3, "%02x", absfs.state[i]);
        strp += res;
    }
    destroy_abstract_fs(&absfs);
    return abs_state_str;
}

static void mount_fs(char *dev, char *mp, char *fs_type)
{
    int ret = -1; 
    int err = 0;
    ret = mount(dev, mp, fs_type, MS_NOATIME, "");
    if (ret != 0) {
        err = errno;
        goto err;
    }
    return;
err:
    umount2(mp, MNT_FORCE);
    fprintf(stderr, "Cannot mount file system %s on %s with mount point %s (%s)\n",
            fs_type, dev, mp, strerror(err));
    exit(1);
}

static void unmount_fs(char *mp, char *fs_type)
{
    bool has_failure = false;
    int retry_limit = 20;
    int ret = -1;
    int err = 0;
try_unmount:
    ret = umount2(mp, 0);
    err = errno;
    if (ret != 0) {
        useconds_t waitms = (100 << (10 - retry_limit));
        if (err == EBUSY && retry_limit > 0) {
            fprintf(stderr, "File system %s mounted on %s is busy. Retry "
                        "unmounting after %dms.\n", fs_type, mp, waitms);
            usleep(1000 * waitms);
            retry_limit--;
            goto try_unmount;
        }
        fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                fs_type, mp, strerror(err));
        has_failure = true;
    }
    if (has_failure)
        exit(1);
}

static int create_file(const char *path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

int main(int argc, char *argv[])
{
    char *mp = NULL;
    char *dev = NULL;
    char *fs_type = NULL;
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <fs-type> <loop_max>\n", argv[0]);
        exit(1);
    }
    mp = argv[1];
    dev = argv[2];
    fs_type = argv[3];
    const long loop_max = atol(argv[4]);
    unsigned int hash_option = 0;

    long loop_id = 0;
    char file_path[PATH_MAX] = {0};
    char dir_path[PATH_MAX] = {0};
    char *state_ptr = NULL; 
    // Start loop based on loop_max
    int ret = -1;
    int err = 0;
    while (loop_id < loop_max) {
        char *absfs_save = NULL;
        char *absfs_restore = NULL;
        // Mount the jffs2 file system
        mount_fs(dev, mp, fs_type);

        // Op. 1 Create a few files
        for (int i = 0; i < MAX_FILES; ++i) {
            snprintf(file_path, PATH_MAX, "%s/file-%d", mp, i);
            ret = create_file(file_path, 0644);
            err = errno;
            if (ret < 0) {
                fprintf(stderr, "create_file %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }
        }

        // Op. 2 Create a few dirs
        for (int i = 0; i < MAX_DIRS; ++i) {
            snprintf(dir_path, PATH_MAX, "%s/dir-%d", mp, i);
            ret = mkdir(dir_path, 0755);
            err = errno;
            if (ret < 0) {
                fprintf(stderr, "mkdir %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }
        }        

        // Calculate fs abstract state
        absfs_save = calloc(ABSFS_LENGTH, sizeof(char));
        absfs_save = get_abstract_state(mp, hash_option, absfs_save);

        // Umount fs
        unmount_fs(mp, fs_type);

        // Save fs state by mmap and memcpy
        state_ptr = NULL;
        do_checkpoint(dev, &state_ptr);
        if (!state_ptr) {
            fprintf(stderr, "State Save Failed\n");
            exit(1);
        }

        // Remove Files and Dirs
        mount_fs(dev, mp, fs_type);
        for (int i = 0; i < MAX_FILES; ++i) {
            snprintf(file_path, PATH_MAX, "%s/file-%d", mp, i);
            ret = unlink(file_path);
            err = errno;
            if (ret < 0) {
                fprintf(stderr, "unlink %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }
        }

        for (int i = 0; i < MAX_DIRS; ++i) {
            snprintf(dir_path, PATH_MAX, "%s/dir-%d", mp, i);
            ret = rmdir(dir_path);
            if (ret < 0) {
                fprintf(stderr, "rmdir %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }            
        }
        unmount_fs(mp, fs_type);

        // Restore fs state
        do_restore(dev, state_ptr);

        // Mount fs (again)
        mount_fs(dev, mp, fs_type);

        // Calculate fs abstract state (again) and compare
        absfs_restore = calloc(ABSFS_LENGTH, sizeof(char));
        absfs_restore = get_abstract_state(mp, hash_option, absfs_restore);

        if (strcmp(absfs_save, absfs_restore) == 0) {
            fprintf(stdout, "%ld Passed.\n", loop_id);
        }
        else {
            fprintf(stdout, "%ld Failed.\n", loop_id);
            exit(1);
        }
        unmount_fs(mp, fs_type);

        // Remove Files and Dirs Again
        mount_fs(dev, mp, fs_type);
        for (int i = 0; i < MAX_FILES; ++i) {
            snprintf(file_path, PATH_MAX, "%s/file-%d", mp, i);
            ret = unlink(file_path);
            err = errno;
            if (ret < 0) {
                fprintf(stderr, "unlink %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }
        }

        for (int i = 0; i < MAX_DIRS; ++i) {
            snprintf(dir_path, PATH_MAX, "%s/dir-%d", mp, i);
            ret = rmdir(dir_path);
            if (ret < 0) {
                fprintf(stderr, "rmdir %d failed, ret = %d, err = %d (%s)\n", 
                    i, ret, err, strerror(err));
                unmount_fs(mp, fs_type);
                exit(1);
            }            
        }
        unmount_fs(mp, fs_type);

        // Clean up
        free(absfs_save);
        free(absfs_restore);
        ++loop_id;
    }
    return 0;
}

