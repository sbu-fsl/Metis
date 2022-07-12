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

//#define ENABLE_LOG

#ifdef ENABLE_LOG
const char *log_file = "mkdir_bug.csv"
#endif
char *state_ptr = NULL; 
char *mp = NULL;
char *dev = NULL;
char *fs_type = NULL;
int err = 0;

static int create_file(const char *path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

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
    // fprintf(stdout, "checkpoint size: %zu\n", fs_size);
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
    // fprintf(stdout, "restore size: %zu\n", size);
	char *ptr;

	ptr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	
	memcpy(ptr, buffer, size);
    free(buffer);

	munmap(ptr, size);
	close(devfd);
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

void mount_fs()
{
    //printf ("Caller name: %pS\n", __builtin_return_address(0));
    int ret = -1; 
    int retry_limit = 1;
try_mount:    
    ret = mount(dev, mp, fs_type, MS_NOATIME, "");
    if (ret != 0) {
        if (errno == EIO && retry_limit > 0) {
            execute_cmd("flash_erase /dev/mtd0 0 0");
            fprintf(stdout, "retry mount...\n");
            retry_limit--;
            goto try_mount;
        }
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

void unmount_fs()
{
    bool has_failure = false;
    int retry_limit = 20;
    int ret = -1;
try_unmount:
    ret = umount2(mp, 0);
    if (ret != 0) {
        useconds_t waitms = (100 << (10 - retry_limit));
        if (errno == EBUSY && retry_limit > 0) {
            fprintf(stderr, "File system %s mounted on %s is busy. Retry "
                        "unmounting after %dms.\n", fs_type, mp, waitms);
            usleep(1000 * waitms);
            retry_limit--;
            goto try_unmount;
        }
        fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                fs_type, mp, strerror(errno));
        has_failure = true;
    }
    if (has_failure)
        exit(1);
}

int main(int argc, char *argv[])
{
    /* Get mountpoint and loop_max from args */
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <fs-type> <loop_max>\n", argv[0]);
        exit(1);
    }
    mp = argv[1];
    dev = argv[2];
    fs_type = argv[3];
    const long loop_max = atol(argv[4]);

    /* Set up log file */
#ifdef ENABLE_LOG
    FILE *logfp = fopen(log_file, "w");
    if (!logfp) {
        fprintf(stderr, "Failed to open log file %s\n", log_file);
        exit(1);
    }
#endif
    long loop_id = 0;
    int rand_num;
    char file_path[PATH_MAX] = {0};
    char dir_path[PATH_MAX] = {0};

    /* umount it first */
    unmount_fs();

    /* Start Loop */
    int ret = -1;
    srand(time(0));
    while (loop_id < loop_max) {
        /* Op. 1 Create a regular file */

        mount_fs();
        rand_num = rand() % 65536;
        snprintf(file_path, PATH_MAX, "%s/test-%d", mp, rand_num);
        errno = 0;
        ret = create_file(file_path, 0644);
        err = errno;
        unmount_fs();
        if (ret < 0) {
            fprintf(stderr, "create_file failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            exit(1);
        }

        /* Op. 2 Checkpoint the current concrete state */
        state_ptr = NULL;
        do_checkpoint(dev, &state_ptr);
        if (!state_ptr) {
            fprintf(stderr, "Checkpoint failed\n");
            exit(1);
        }

        /* Op. 3 Unlink the file */
        mount_fs();
        errno = 0;
        ret = unlink(file_path);
        err = errno;
        unmount_fs();
        if (ret < 0) {
            fprintf(stderr, "unlink failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            exit(1);
        }

        /* Op. 4 Restore to the previous concrete state */
        do_restore(dev, state_ptr);
        /* statfs before mkdir */

        /* Op. 5 Create a directory */
        mount_fs();
        snprintf(dir_path, PATH_MAX, "%s/testdir-%d", mp, rand_num);
        errno = 0;
        ret = mkdir(dir_path, 0755);
        err = errno;
        unmount_fs();
        if (ret < 0) {
            fprintf(stderr, "mkdir failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            exit(1);
        }

        /* statfs after mkdir */

        /* If the regular file does not exist, there is a bug */
        mount_fs();
        if (access(file_path, F_OK) != 0) {
            fprintf(stderr, "[BUG] jffs2 mkdir bug reproduced!\n");
            unmount_fs();
            exit(1);
        }

        /* Cleanup: remove the file and directory */
        errno = 0;
        ret = unlink(file_path);
        err = errno;
        unmount_fs();
        if (ret < 0) {
            fprintf(stderr, "unlink (cleanup) failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            exit(1);
        }        

        mount_fs();
        errno = 0;
        ret = rmdir(dir_path);
        err = errno;
        unmount_fs();
        if (ret < 0) {
            fprintf(stderr, "rmdir failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            exit(1);
        }
        printf("loop id: %ld passed!\n", loop_id);
        ++loop_id;
    }
#ifdef ENABLE_LOG
    fclose(logfp);
#endif
    return 0;
}


