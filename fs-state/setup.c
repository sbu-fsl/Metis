#include "fileutil.h"
#include <sys/wait.h>

void execute_cmd(const char *cmd)
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

int check_device(const char *devname, const size_t exp_size_kb)
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

int setup_generic(const char *fsname, const char *devname, const size_t size_kb)
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

int setup_jffs2(const char *devname, const size_t size_kb)
{
    char cmdbuf[PATH_MAX];
    int ret, randnum;
    
    // check if mtdram and mtdblock are loaded
    execute_cmd("lsmod | grep mtdram");
    execute_cmd("lsmod | grep mtdblock");

    // check if the device is ready
    ret = check_device(devname, size_kb);
    if (ret != 0) {
        fprintf(stderr, "Cannot setup jffs2 because %s is bad or not ready.\n",
                devname);
        return ret;
    }
    // create an empty jffs2 image
    // first prepare an empty directory
    srand(time(0));
    randnum = rand() % 65536;
    snprintf(cmdbuf, PATH_MAX, "mkdir -p /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    // make the jffs2 image according to the empty directory created
    snprintf(cmdbuf, PATH_MAX, "mkfs.jffs2 --pad=%zu --root=/tmp/_empty_dir_%d"
             " -o /tmp/jffs2_%d.img", size_kb * 1024, randnum, randnum);
    execute_cmd(cmdbuf);
    // write the image to the mtd block device
    snprintf(cmdbuf, PATH_MAX, "dd if=/tmp/jffs2_%d.img of=%s bs=1k count=%zu "
             "status=none", randnum, devname, size_kb);
    execute_cmd(cmdbuf);
    // cleanup
    snprintf(cmdbuf, PATH_MAX, "rm -r /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    snprintf(cmdbuf, PATH_MAX, "rm /tmp/jffs2_%d.img", randnum);
    execute_cmd(cmdbuf);
    return 0;
}

void populate_mountpoints()
{
    char cmdbuf[PATH_MAX];
    for (int i = 0; i < get_n_fs(); ++i) {
        snprintf(cmdbuf, PATH_MAX, "mkdir -p /mnt/test-%s%s", fslist[i],
                 fssuffix[i]);
        execute_cmd(cmdbuf);
        unmount_all_relaxed();
    }
}
