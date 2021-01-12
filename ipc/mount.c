#define _XOPEN_SOURCE 500
#define _POSIX_C_SOURCE 2
#include "fileutil.h"

static bool fs_frozen[N_FS] = {0};

static char *receive_output(FILE *cmdfp, size_t *length)
{
    const size_t block = 4096;
    char *buffer = malloc(block);
    size_t readsz = 0, bufsz = block;
    assert(buffer);
    while (!feof(cmdfp)) {
        if (readsz + block > bufsz) {
            char *newbuf = realloc(buffer, bufsz + block);
            if (!newbuf) {
                fprintf(stderr, "%s encountes out-of-memory issue, command "
                        "output is truncated at %zu bytes.\n", __func__,
                        readsz);
                break;
            }
            bufsz += block;
            buffer = newbuf;
        }
        char *ptr = buffer + readsz;
        readsz += fread(ptr, 1, block, cmdfp);
    }
    *length = readsz;
    return buffer;
}

bool do_fsck()
{
    char cmdbuf[ARG_MAX];
    bool isgood = true;
    for (int i = 0; i < N_FS; ++i) {
        snprintf(cmdbuf, ARG_MAX, "fsck -N -t %s %s 2>&1", fslist[i],
                 devlist[i]);
        FILE *cmdfp = popen(cmdbuf, "r");
        size_t outlen = 0;
        char *output = receive_output(cmdfp, &outlen);
        int ret = pclose(cmdfp);
        if (ret != 0) {
            fprintf(stderr, "fsck %s failed and returned %d, %s may have been "
                    "corrupted.\n", devlist[i], ret, fslist[i]);
            fprintf(stderr, "Here's the output: \n");
            fwrite(output, 1, outlen, stderr);
            fprintf(stderr, "\n");
            isgood = false;
        }
        free(output);
    }
    return isgood;
}

void clear_excluded_files()
{
    char path[PATH_MAX] = {0};
    const char *folder;
    struct stat st;
    int n = 0, ret;
    mountall();
    while ((folder = exclude_dirs[n]) != NULL) {
        for (int i = 0; i < N_FS; ++i) {
            snprintf(path, PATH_MAX, "/mnt/test-%s/%s", fslist[i], folder);
            ret = stat(path, &st);
            if (ret < 0)
                continue;
            if (S_ISDIR(st.st_mode))
                rmdir(path);
            else
                unlink(path);
        }
        n++;
    }
    unmount_all();
}

void mountall()
{
    int failpos, err;
    for (int i = 0; i < N_FS; ++i) {
        /* Skip crmfs */
        if (strcmp(fslist[i], "crmfs") == 0)
            continue;
        /* mount(source, target, fstype, mountflags, option_str) */
        int ret = mount(devlist[i], basepaths[i], fslist[i], MS_NOATIME, "");
        if (ret != 0) {
            failpos = i;
            err = errno;
            goto err;
        }
    }
    return;
err:
    /* undo mounts */
    for (int i = 0; i < failpos; ++i) {
        umount2(basepaths[i], MNT_FORCE);
    }
    fprintf(stderr, "Could not mount file system %s in %s at %s (%s)\n",
            fslist[failpos], devlist[failpos], basepaths[failpos],
            errnoname(err));
    exit(1);
}

void unmount_all()
{
    bool has_failure = false;
    int ret;
    for (int i = 0; i < N_FS; ++i) {
        if (strcmp(fslist[i], "crmfs") == 0)
            continue;
        int retry_limit = 10;
        /* We have to unfreeze the frozen file system before unmounting it.
         * Otherwise the system will hang! */
        if (fs_frozen[i]) {
            fsthaw(fslist[i], devlist[i], basepaths[i]);
        }
try_unmount:
        ret = umount2(basepaths[i], 0);
        if (ret != 0) {
            /* If unmounting failed due to device being busy, wait 1ms and
             * try again up to retry_limit times */
            if (errno == EBUSY && retry_limit > 0) {
                fprintf(stderr, "File system %s mounted on %s is busy. Retry "
                        "unmounting after 1ms.\n", fslist[i], basepaths[i]);
                usleep(1000);
                retry_limit--;
                goto try_unmount;
            }
            fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                    fslist[i], basepaths[i], errnoname(errno));
            has_failure = true;
        }
    }
    if (has_failure)
        exit(1);
}

static const int warning_limits = N_FS;
static int warnings_issued = 0;

static void set_fs_frozen_flag(const char *mountpoint, bool value)
{
    for (int i = 0; i < N_FS; ++i) {
        if (strncmp(basepaths[i], mountpoint, PATH_MAX) == 0) {
            fs_frozen[i] = value;
            break;
        }
    }
}

static int freeze_or_thaw(const char *caller, const char *fstype,
    const char *devpath, const char *mp, unsigned long op)
{
    if (op != FIFREEZE && op != FITHAW)
        return -1;

    char *opname;
    int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0) {
        fprintf(stderr, "%s: Cannot open %s (%s)\n", caller, mp,
                errnoname(errno));
        return -1;
    }

    if (op == FIFREEZE)
        opname = "FIFREEZE";
    else if (op == FITHAW)
        opname = "FITHAW";

    int ret = ioctl(mpfd, op, 0);
    int err = errno;
    close(mpfd);
    if (ret == 0) {
        /* Mark the corresponding file system as being frozen */
        set_fs_frozen_flag(mp, (op == FIFREEZE));
        return 0;
    }
    /* fall back to remounting the file system in read-only mode */
    if (warnings_issued < warning_limits) {
        fprintf(stderr, "%s: ioctl %s cannot be used on %s (%s). "
                "Falling back to remounting in r/o mode.\n", caller, opname,
                mp, errnoname(err));
        warnings_issued++;
    }

    int remnt_flag = MS_REMOUNT | MS_NOATIME;
    char *options = "";
    if (op == FIFREEZE)
        remnt_flag |= MS_RDONLY;
    else
        options = "rw";

    ret = mount(devpath, mp, fstype, remnt_flag, options);
    if (ret < 0) {
        fprintf(stderr, "%s: remounting failed on %s (%s)\n", caller, mp,
                errnoname(errno));
    }
    return (ret == 0) ? 0 : -1;

}

int fsfreeze(const char *fstype, const char *devpath, const char *mountpoint)
{
    return freeze_or_thaw(__func__, fstype, devpath, mountpoint, FIFREEZE);
}

int fsthaw(const char *fstype, const char *devpath, const char *mountpoint)
{
    return freeze_or_thaw(__func__, fstype, devpath, mountpoint, FITHAW);
}

int unfreeze_all()
{
    for (int i = 0; i < N_FS; ++i) {
        if (fs_frozen[i]) {
            fprintf(stderr, "unfreezing %s at %s\n", fslist[i], basepaths[i]);
            fsthaw(fslist[i], devlist[i], basepaths[i]);
        }
    }
}