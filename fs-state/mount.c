#include "fileutil.h"

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
                 basepaths[i]);
        FILE *cmdfp = popen(cmdbuf, "r");
        size_t outlen = 0;
        char *output = receive_output(cmdfp, &outlen);
        int ret = pclose(cmdfp);
        if (ret != 0) {
            fprintf(stderr, "fsck %s failed and returned %d, %s may have been "
                    "corrupted.\n", basepaths[i], ret, fslist[i]);
            fprintf(stderr, "Here's the output: \n");
            fwrite(output, 1, outlen, stderr);
            fprintf(stderr, "\n");
            isgood = false;
        }
        free(output);
    }
    return isgood;
}

void mountall()
{
    bool inited = false;
    int failpos, err;
    for (int i = 0; i < N_FS; ++i) {
        /* mount(source, target, fstype, mountflags, option_str) */
        int ret = mount(devlist[i], basepaths[i], fslist[i], MS_NOATIME, "");
        if (ret != 0) {
            failpos = i;
            err = errno;
            goto err;
        }
    }
    if (inited)
        return;
    /* remove all folders specified in the exclusion list in config.h */
    int n = 0;
    const char *folder;
    char fullpath[PATH_MAX];
    while ((folder = exclude_dirs[n])) {
        for (int i = 0; i < N_FS; ++i) {
            snprintf(fullpath, PATH_MAX, "%s/%s", basepaths[i], folder);
            rmdir(fullpath);
        }
        n++;
    }
    inited = true;
    return;
err:
    /* undo mounts */
    for (int i = 0; i < failpos; ++i) {
        umount2(basepaths[i], MNT_FORCE);
    }
    fprintf(stderr, "Could not mount file system %s in %s at %s (%s)\n",
            fslist[failpos], devlist[failpos], basepaths[failpos],
            errnoname(err));
    abort();
}

void unmount_all()
{
    bool has_failure = false;
    int ret;
#ifndef NO_FS_STAT
    record_fs_stat();
#endif
    assert(do_fsck());
    for (int i = 0; i < N_FS; ++i) {
        int retry_limit = 10;
try_unmount:
        ret = umount2(basepaths[i], 0);
        if (ret != 0) {
            /* If unmounting failed due to device being busy, wait 1ms and
             * try again up to retry_limit times */
            if (errno == EBUSY && retry_limit > 0) {
                usleep(1000);
                retry_limit--;
                goto try_unmount;
            }
            fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                    fslist[i], basepaths[i], errnoname(errno));
            has_failure = true;
        }
    }
    assert(!has_failure);
}

