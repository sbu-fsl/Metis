#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <linux/fs.h>
#include <unistd.h>
#include <sys/vfs.h>

char *state_ptr = NULL; 
char *mp = NULL;
char *dev = NULL;
char *fs_type = NULL;
int err = 0;
int ret = -1;

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
    int err = 0;
    ret = mount(dev, mp, fs_type, MS_NOATIME, "");
    if (ret != 0) {
        err = errno;
        if (err == EIO) {
            fprintf(stderr, "EIO issue in JFFS2 reproduced.\n");
        }
        fprintf(stderr, "Cannot mount file system %s on %s with mount point %s; ret = %d, err = %d (%s)\n",
            fs_type, dev, mp, ret, err, strerror(err));
        exit(1);
    }
    return;
}

void unmount_fs()
{
    int ret = -1;
    int err = 0;
    ret = umount2(mp, 0);
    err = errno;
    if (ret != 0) {
        fprintf(stderr, "Could not unmount file system %s at %s; ret = %d, err = %d (%s)\n",
                fs_type, mp, ret, err, strerror(err));
        exit(1);
    }
}

int main(int argc, char *argv[])
{
    /* Get mountpoint, dev, mountpoint and loop_max from args */
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <fs-type> <loop_max>\n", argv[0]);
        exit(1);
    }
    mp = argv[1];
    dev = argv[2];
    fs_type = argv[3];
    const long loop_max = atol(argv[4]);

    long loop_id = 0;
    char file_path[PATH_MAX] = {0};

    /* umount it first */
    unmount_fs();

    /* Start Loop */
    snprintf(file_path, PATH_MAX, "%s/test_f", mp);
    while (loop_id < loop_max) {
        /* Op. 1 Create a regular file */
        mount_fs();

        errno = 0;
        ret = create_file(file_path, 0644);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "create_file failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
        unmount_fs();

        /* Op. 2 Unlink the file */
        mount_fs();
        
        errno = 0;
        ret = unlink(file_path);
        err = errno;
        if (ret < 0) {
            fprintf(stderr, "unlink failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
            unmount_fs();
            exit(1);
        }
        unmount_fs();

        fprintf(stdout, "loop id: %ld passed\n", loop_id);
        ++loop_id;
    }
    return 0;
}
