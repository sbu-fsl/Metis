#include "fileutil.h"
#include <sys/wait.h>

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

static int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

static int check_device(const char *devname, const size_t exp_size_kb)
{
    int fd = open(devname, O_RDONLY);
    struct stat devinfo;
    if (fd < 0) {
        fprintf(stderr, "Cannot open %s (err=%s, %d)\n",
                devname, errnoname(errno), errno);
        return -errno;
    }
    int retval = fstat(fd, &devinfo);
    if (retval < 0) {
        fprintf(stderr, "Cannot stat %s (err=%s, %d)\n",
                devname, errnoname(errno), errno);
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

static int setup_generic(const char *fsname, const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    ret = check_device(devname, size_kb);
    if (ret != 0) {
        fprintf(stderr, "Cannot setup %s because %s is bad or not ready.\n",
                fsname, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
            "dd if=/dev/zero of=%s bs=1k count=%zu status=none",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.%s %s", fsname, devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_mtd(const size_t size_kb)
{
    char cmdbuf[PATH_MAX];

    snprintf(cmdbuf, PATH_MAX, "mtdram total_size=%ld erase_size=16", size_kb / 1024);
    execute_cmd(cmdbuf);
    snprintf(cmdbuf, PATH_MAX, "mtdblock");
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_jffs2(const char *devname, const size_t size_kb)
{
    char cmdbuf[PATH_MAX];
    int ret, randnum;
    int failCount = 0;

    // check if mtdram and mtdblock are loaded
    execute_cmd("lsmod | grep mtdram");
    execute_cmd("lsmod | grep mtdblock");

mtd_check:
    // check if the device is ready
    ret = check_device(devname, size_kb);
    if (ret != 0)
    {
        if (failCount > 2)
        {
            fprintf(stderr, "Cannot setup jffs2 because %s is bad or not ready.\n",
                    devname);
            return ret;
        }
        else
        {
            failCount++;
            setup_mtd(size_kb);
            goto mtd_check;
        }
    }
    // create an empty jffs2 image
    // first prepare an empty directory
    srand(time(0));
    randnum = rand() % 65536;
    snprintf(cmdbuf, PATH_MAX, "mkdir -p /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    // make the jffs2 image according to the empty directory created
    snprintf(cmdbuf, PATH_MAX, "mkfs.jffs2 --pad=%zu --root=/tmp/_empty_dir_%d"
                               " -o /tmp/jffs2_%d.img",
             size_kb * 1024, randnum, randnum);
    execute_cmd(cmdbuf);
    // write the image to the mtd block device
    snprintf(cmdbuf, PATH_MAX, "dd if=/tmp/jffs2_%d.img of=%s bs=1k count=%zu "
                               "status=none",
             randnum, devname, size_kb);
    execute_cmd(cmdbuf);
    // cleanup
    snprintf(cmdbuf, PATH_MAX, "rm -r /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    snprintf(cmdbuf, PATH_MAX, "rm /tmp/jffs2_%d.img", randnum);
    execute_cmd(cmdbuf);
    return 0;
}

static void populate_mountpoints()
{
    char check_mount_cmdbuf[PATH_MAX];
    char unmount_cmdbuf[PATH_MAX];
    char check_mp_exist_cmdbuf[PATH_MAX];
    char rm_mp_cmdbuf[PATH_MAX];
    char mk_mp_cmdbuf[PATH_MAX];
    for (int i = 0; i < get_n_fs(); ++i) {
        snprintf(check_mount_cmdbuf, PATH_MAX, "mount | grep %s", get_basepaths()[i]);    
        /* If the mountpoint has fs mounted, then unmount it */
        if (execute_cmd_status(check_mount_cmdbuf) == 0) {
            snprintf(unmount_cmdbuf, PATH_MAX, "umount -f %s", get_basepaths()[i]);
            execute_cmd(unmount_cmdbuf);
        }

        snprintf(check_mp_exist_cmdbuf, PATH_MAX, "test -f %s", get_basepaths()[i]);
        /* If the mountpoint exists, then remove it */
        if (execute_cmd_status(check_mp_exist_cmdbuf) == 0) {
            snprintf(rm_mp_cmdbuf, PATH_MAX, "rm -r %s", get_basepaths()[i]);
            execute_cmd(rm_mp_cmdbuf);         
        }

        snprintf(mk_mp_cmdbuf, PATH_MAX, "mkdir -p %s", get_basepaths()[i]);
        execute_cmd(mk_mp_cmdbuf);
    }
}

static int setup_f2fs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 40 MiB
    ret = check_device(devname, 40 * 1024);
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
    snprintf(cmdbuf, PATH_MAX, "mkfs.f2fs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_btrfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 110 MiB
    ret = check_device(devname, 110 * 1024);
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
    snprintf(cmdbuf, PATH_MAX, "mkfs.btrfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_xfs(const char *devname, const size_t size_kb)
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
    snprintf(cmdbuf, PATH_MAX, "mkfs.btrfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_verifs1(int i)
{
    char cmdbuf[PATH_MAX];

    snprintf(cmdbuf, PATH_MAX, "crmfs %s", get_basepaths()[i]);
    execute_cmd(cmdbuf);
    return 0;
}

static int setup_verifs2(int i)
{
    char cmdbuf[PATH_MAX];

    snprintf(cmdbuf, PATH_MAX, "mount -t fuse.fuse-cpp-ramfs verifs2 %s", get_basepaths()[i]);
    execute_cmd(cmdbuf);
    return 0;
}

void setup_filesystems()
{
    int ret;
    populate_mountpoints();
    for (int i = 0; i < get_n_fs(); ++i)
    {
        if (strcmp(get_fslist()[i], "jffs2") == 0)
        {
            ret = setup_jffs2(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "f2fs") == 0)
        {
            ret = setup_f2fs(get_devlist()[i], get_devsize_kb()[i] / 1024);
        }
        else if (strcmp(get_fslist()[i], "btrfs") == 0)
        {
            ret = setup_btrfs(get_devlist()[i], get_devsize_kb()[i] / 1024);
        }
        else if (strcmp(get_fslist()[i], "xfs") == 0)
        {
            ret = setup_xfs(get_devlist()[i], get_devsize_kb()[i] / 1024);
        }
        // TODO: we need to consider VeriFS1 and VeriFS2 separately here
        else if (is_verifs(get_fslist()[i]))
        {
            const char *fsname = get_fslist()[i];
            size_t strlen = strnlen(fsname, PATH_MAX);
            switch (fsname[strlen - 1])
            {
            case '1':
                ret = setup_verifs1(i);
                break;
            case '2':
                ret = setup_verifs2(i);
                break;
            }
        }
        else
        {
            ret = setup_generic(get_fslist()[i], get_devlist()[i], get_devsize_kb()[i]);
        }
        if (ret != 0)
        {
            fprintf(stderr, "Cannot setup file system %s (ret = %d)\n",
                    get_fslist()[i], ret);
            exit(1);
        }
    }
}
