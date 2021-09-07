#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <linux/limits.h>
#include <sys/stat.h>
#include <sys/mount.h>
#include <sys/vfs.h>

int create_file(const char* path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0)
    {
        close(fd);
    }
    return fd >= 0 ? 0 : -1;
}


ssize_t write_file(const char *path, char *data, off_t offset, size_t length)
{
    int fd = open(path, O_RDWR);
    int err;
    if (fd < 0)
    {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1)
    {
        err = errno;
        goto exit_write_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0)
    {
        err = errno;
        goto exit_write_err;
    }
    if (writesz < length)
    {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return writesz;

exit_write_err:
    close(fd);
    errno = err;
    return -1;
}

int truncate_file(const char *path, off_t length)
{
    return truncate(path, length);
}

int unlink_file(const char *path)
{
    return unlink(path);
}

int create_dir(const char *path, int mode)
{
    return mkdir(path, mode);
}

int remove_dir(const char *path)
{
    return rmdir(path);
}

int freeze_or_thaw_fs(const char *mount_point, unsigned long op)
{
    int mpfd = open(mount_point, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0)
    {
        return -1;
    }
    int ret = ioctl(mpfd, op, 0);
    int err;

    if (ret != 0)
    {
        err = errno;
        goto freeze_or_thaw_err_exit;
    }
    close(mpfd);
    return ret;

freeze_or_thaw_err_exit:
    close(mpfd);
    errno = err;
    return ret;
}

int mount_fs(const char *source, const char *target,
            const char *filesystemtype, unsigned long mountflags,
            const void *data)
{
    return mount(source, target, filesystemtype, mountflags, data);
}

int umount_fs(const char *target, int flags)
{
    return umount2(target, flags);
}

int get_fs_free_spaces(char *path)
{
    struct statfs fsinfo;
    int ret = statfs(path, &fsinfo);
    if (ret == 0)
    {
        size_t free_spc = fsinfo.f_bfree * fsinfo.f_bsize;
        FILE *f = fopen("/mnt/hgfs/mcfs_shared/ret/fs_free_space_ret", "w");
        fprintf(f, "%zu", free_spc);
        fclose(f);
    }
    return ret;
}

int write_dummy_file(char *path, size_t fillsz)
{
    const char *dummy_file = ".mcfs_dummy";
    char fullpath[PATH_MAX] = {0};
    snprintf(fullpath, PATH_MAX, "%s/%s", path, dummy_file);

    /* Create/open the dummy file */
    int fd = open(fullpath, O_CREAT | O_TRUNC | O_RDWR, 0666);
    if (fd < 0)
    {
        return -1;
    }
    /* Start filling */
    memset(fullpath, 0, PATH_MAX);
    while (fillsz > 0)
    {
        size_t writesz = fillsz < PATH_MAX ? fillsz : PATH_MAX;
        ssize_t ret = write(fd, fullpath, writesz);
        if (ret < 0)
        {
            return -2;
        }
        fillsz -= ret;
    }
    close(fd);
    return 0;
}

int main(int argc, char** argv)
{
    int ret = -1;
    errno = 0;
    if (argc > 1) {
        char* op = argv[1];
        if (strcmp(op, "create_file") == 0)
        {
            int mode = atoi(argv[3]);
            ret = create_file(argv[2], mode);
        }
        else if (strcmp(op, "write_file") == 0)
        {
            char *data;
            off_t offset;
            size_t length;
            if (argc == 6)
            {
                data = argv[3];
                offset = strtol(argv[4], NULL, 10);
                length = (size_t) strtoull(argv[5], NULL, 10);
            }
            else
            {
                data = NULL;
                offset = strtol(argv[3], NULL, 10);
                length = (size_t) strtoull(argv[4], NULL, 10);
            }
            ret = write_file(argv[2], data, offset, length);
        }
        else if (strcmp(op, "truncate_file") == 0)
        {
            off_t length = strtol(argv[3], NULL, 10);
            ret = truncate_file(argv[2], length);
        }
        else if (strcmp(op, "unlink_file") == 0)
        {
            ret = unlink_file(argv[2]);
        }
        else if (strcmp(op, "create_dir") == 0)
        {
            int mode = atoi(argv[3]);
            ret = create_dir(argv[2], mode);
        }
        else if (strcmp(op, "remove_dir") == 0)
        {
            ret = remove_dir(argv[2]);
        }
        else if (strcmp(op, "freeze_or_thaw_fs") == 0)
        {
            unsigned long op = strtoul(argv[3], NULL, 10);
            ret = freeze_or_thaw_fs(argv[2], op);
        }
        else if (strcmp(op, "mount_fs") == 0)
        {
            unsigned long mountflags = strtoul(argv[5], NULL, 10);
            if (argc == 6)
            {
                ret = mount_fs(argv[2], argv[3], argv[4], mountflags, "");
            }
            else
            {
                ret = mount_fs(argv[2], argv[3], argv[4], mountflags, argv[6]);
            }
        }
        else if (strcmp(op, "umount_fs") == 0)
        {
            int flags = strtol(argv[3], NULL, 10);
            ret = umount_fs(argv[2], flags);
        }
        else if (strcmp(op, "get_fs_free_spaces") == 0)
        {
            ret = get_fs_free_spaces(argv[2]);
        }
        else if (strcmp(op, "write_dummy_file") == 0)
        {
            size_t fillsz = (size_t) strtoull(argv[3], NULL, 10);
            ret = write_dummy_file(argv[2], fillsz);
        }
    }

    int err = errno;
    FILE *f = fopen("/mnt/hgfs/mcfs_shared/ret/mcfs_fops_ret", "w");
    fprintf(f, "%d %d", ret, err);
    fclose(f);

    return ret;
}

