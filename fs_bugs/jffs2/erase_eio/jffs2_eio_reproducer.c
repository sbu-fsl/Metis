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

char *state_ptr = NULL; 
char *mp = NULL;
char *dev = NULL;
char *fs_type = NULL;
int err = 0;

#define REMOUNT_EVERY_OPS

static int create_file(const char *path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

void mount_fs()
{
    int ret = -1; 
    int retry_limit = 1;
    int err = 0;
try_mount:    
    ret = mount(dev, mp, fs_type, MS_NOATIME, "");
    if (ret != 0) {
        if (errno == EIO) {
            fprintf(stdout, "EIO issue in jffs2 reproduced.\n");
            exit(1);
        }
        if (retry_limit > 0) {
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

    long loop_id = 0;
    int rand_num;
    char file_path[PATH_MAX] = {0};
    char dir_path[PATH_MAX] = {0};

    /* umount it first */
#ifdef REMOUNT_EVERY_OPS
    unmount_fs();
#endif

    /* Start Loop */
    int ret = -1;
    srand(time(0));
    while (loop_id < loop_max) {
        /* Op. 1 Create a regular file */
#ifdef REMOUNT_EVERY_OPS
        mount_fs();
#endif
        rand_num = rand() % 65536;
        snprintf(file_path, PATH_MAX, "%s/test-%d", mp, rand_num);
        errno = 0;
        ret = create_file(file_path, 0644);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "create_file failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
#ifdef REMOUNT_EVERY_OPS
        unmount_fs();
#endif
        /* Op. 2 Unlink the file */
#ifdef REMOUNT_EVERY_OPS
        mount_fs();
#endif
        errno = 0;
        ret = unlink(file_path);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "unlink failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
#ifdef REMOUNT_EVERY_OPS
        unmount_fs();
#endif

        /* Op. 3 Create a directory */
#ifdef REMOUNT_EVERY_OPS
        mount_fs();
#endif
        snprintf(dir_path, PATH_MAX, "%s/testdir-%d", mp, rand_num);
        errno = 0;
        ret = mkdir(dir_path, 0755);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "mkdir failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
#ifdef REMOUNT_EVERY_OPS
        unmount_fs();
#endif

        /* Op. 4 Remove the directory */    
#ifdef REMOUNT_EVERY_OPS 
        mount_fs();
#endif
        errno = 0;
        ret = rmdir(dir_path);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "rmdir failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
#ifdef REMOUNT_EVERY_OPS 
        unmount_fs();
#endif
        fprintf(stdout, "loop id: %ld passed\n", loop_id);
        ++loop_id;
    }
    return 0;
}
