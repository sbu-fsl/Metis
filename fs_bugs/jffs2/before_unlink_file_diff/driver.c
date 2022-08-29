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

/* write to path, at offset, for len bytes, value "byte" */
int main(int argc, char *argv[])
{
    char *path = argv[1];
    int offset = atoi(argv[2]);
    ssize_t len = atoi(argv[3]);
    int byte = atoi(argv[4]);

    mp = argv[5];
    dev = argv[6];
    fs_type = argv[7];

    int ret = -1;
    int fd = open(path, O_RDWR|O_CREAT);
    if (fd < 0) {
      perror(path);
      exit(1);
    }

    off_t res = lseek(fd, offset, SEEK_SET);
    if (res < 0) {
      perror("lseek");
      exit(1);
    }

    char *data = malloc(len);
    if (data == NULL) {
      errno = ENOMEM;
      perror("malloc");
      exit(1);
    }
    memset(data, byte, len);

    ssize_t writesz = write(fd, data, len);
    if (writesz < 0) {
      perror("write");
      exit(1);
    }
    if (writesz < len) {
      fprintf(stderr, "Note: less data written than expected (%ld < %ld)\n",
	      writesz, len);
      exit(1);
    }

    close(fd);
    unmount_fs(mp, fs_type);

    // Checkpoint the write state
    state_ptr = NULL;
    do_checkpoint(dev, &state_ptr);
    if (!state_ptr) {
        fprintf(stderr, "Checkpoint failed\n");
        exit(1);
    }
    // create_file
    mount_fs(dev, mp, fs_type);
    errno = 0;
    ret = create_file(path, 0644);
    err = errno;
    unmount_fs(mp, fs_type);
    if (ret < 0) {
        fprintf(stderr, "create_file failed, ret = %d, err = %d (%s)\n", ret, err, strerror(err));
        exit(1);
    }

    // Restore state
    do_restore(dev, state_ptr);
    do_checkpoint(dev, &state_ptr);
    mount_fs(dev, mp, fs_type);
    exit(0);
}
