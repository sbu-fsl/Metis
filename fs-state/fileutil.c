#include "fileutil.h"

int cur_pid;
char func[FUNC_NAME_LEN + 1];
struct timespec begin_time;

int _opened_files[1024];
int _n_files;
size_t count;

int compare_file_content(const char *path1, const char *path2)
{
    const size_t bs = 4096;
    char buf1[bs], buf2[bs];
    struct stat f1, f2;
    int fd1 = -1, fd2 = -1, ret = 0;
    /* Open the two files */
    fd1 = open(path1, O_RDONLY);
    if (fd1 < 0) {
        fprintf(stderr, "[seqid=%zu] %s: cannot open %s (%s)\n",
                count, __func__, path1, errnoname(errno));
        return -1;
    }
    fd2 = open(path2, O_RDONLY);
    if (fd2 < 0) {
        fprintf(stderr, "[seqid=%zu] %s: cannot open %s (%s)\n",
                count, __func__, path1, errnoname(errno));
        close(fd1);
        return -1;
    }
    /* Get file properties: Make sure equal file size */
    ret = fstat(fd1, &f1);
    if (ret) {
        fprintf(stderr, "[seqid=%zu] %s: fstat '%s' failed (%s)\n",
                count, __func__, path1, errnoname(errno));
        ret = -1;
        goto end;
    }
    ret = fstat(fd2, &f2);
    if (ret) {
        fprintf(stderr, "[seqid=%zu] %s: fstat '%s' failed (%s)\n",
                count, __func__, path2, errnoname(errno));
        ret = -1;
        goto end;
    }
    if (f1.st_size != f2.st_size) {
        fprintf(stderr, "[seqid=%zu] %s: '%s' and '%s' size differ. "
                "'%s' has %zu bytes and '%s' has %zu.\n", count, __func__,
                path1, path2, path1, f1.st_size, path2, f2.st_size);
        ret = 1;
        goto end;
    }
    /* Compare the file content */
    int r1, r2;
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
            fprintf(stderr, "[seqid=%zu] %s: content in '%s' and '%s' "
                    "is not equal.\n", count, __func__, path1, path2);
            ret = -1;
	    break;
        }
    }
    if (r1 < 0 || r2 < 0) {
        fprintf(stderr, "[seqid=%zu] %s: error occurred when reading: %s\n",
                count, __func__, errnoname(errno));
        ret = -1;
    }
end:
    if (fd1 >= 0)
        close(fd1);
    if (fd2 >= 0)
        close(fd2);
    return ret;
}

bool compare_equality_values(char **fses, int n_fs, int *nums)
{
    bool res = true;
    int base = nums[0];
    for (int i = 0; i < n_fs; ++i) {
        if (nums[i] != base) {
            res = false;
            break;
        }
    }
    if (!res) {
        fprintf(stderr, "[seqid=%zu] %s: discrepancy in values found:\n",
                count, __func__);
        for (int i = 0; i < n_fs; ++i)
            fprintf(stderr, "[%s]: %d\n", fses[i], nums[i]);
    }
    return res;
}

void dump_absfs(const char *basepath)
{
    absfs_t absfs;
    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, true, stderr);
}

bool compare_equality_absfs(char **fses, int n_fs, absfs_state_t *absfs)
{
    bool res = true;
    absfs_state_t base;
    memcpy(base, absfs[0], sizeof(absfs_state_t));
    for (int i = 1; i < n_fs; ++i) {
        if (memcmp(base, absfs[i], sizeof(absfs_state_t)) != 0) {
            res = false;
            break;
        }
    }
    if (!res) {
        fprintf(stderr, "[seqid=%zu] Discrepancy in abstract states found:\n",
                count);
        for (int i = 0; i < n_fs; ++i) {
            fprintf(stderr, "[seqid=%zu, fs=%s]: Directory structure:\n",
                    count, fses[i]);
            dump_absfs(basepaths[i]);
            fprintf(stderr, "[seqid=%zu, fs=%s]: hash=", count, fses[i]);
            print_abstract_fs_state(stderr, absfs[i]);
            fprintf(stderr, "\n");
        }
    }
    return res;
}

bool compare_equality_fexists(char **fses, int n_fs, char **fpaths)
{
    bool res = true;
    bool fexists[n_fs];

    /* Check file existence */
    for (int i = 0; i < n_fs; ++i)
        fexists[i] = check_file_existence(fpaths[i]);

    bool base = fexists[0];
    for (int i = 0; i < n_fs; ++i) {
        if (fexists[i] != base) {
            res = false;
            break;
        }
    }
    if (!res) {
        fprintf(stderr, "[%zu] Discrepancy in existence of files found:\n",
                count);
        for (int i = 0; i < n_fs; ++i) {
            fprintf(stderr, "[%s]: %s: %d\n", fses[i], fpaths[i], fexists[i]);
        }
    }
    return res;
}

bool compare_equality_fcontent(char **fses, int n_fs, char **fpaths)
{
    bool res = true;

    if (!compare_equality_fexists(fses, n_fs, fpaths))
        return false;

    /* If none of the files exists, return TRUE */
    if (check_file_existence(fpaths[0]) == false)
        return true;

    for (int i = 1; i < n_fs; ++i) {
        if (compare_file_content(fpaths[i-1], fpaths[i]) != 0) {
            if (res)
                res = false;
            fprintf(stderr, "[seqid=%zu] [%s] (%s) is different from [%s] "
                    "(%s)\n", count, fses[i-1], fpaths[i-1], fses[i],
                    fpaths[i]);
        }
    }
    return res;
}

void show_open_flags(uint64_t flags)
{
    /* RDONLY, WRONLY and RDWR */
    if ((flags & O_ACCMODE) == 0) {
        printf("O_RDONLY ");
    } else {
        if (flags & O_WRONLY)
            printf("O_WRONLY ");
        if (flags & O_RDWR)
            printf("O_RDWR ");
    }

    if (flags & O_CREAT)
        printf("O_CREAT ");
    if (flags & O_EXCL)
        printf("O_EXCL ");
    if (flags & O_TRUNC)
        printf("O_TRUNC ");
    if (flags & O_APPEND)
        printf("O_APPEND ");
    if (flags & O_NONBLOCK)
        printf("O_NONBLOCK ");
    if (flags & O_SYNC)
        printf("O_SYNC ");
    if (flags & O_ASYNC)
        printf("O_ASYNC ");
}

int myopen(const char *pathname, int flags, mode_t mode)
{
    int fd = open(pathname, flags, mode);
    if (fd >= 0) {
        _opened_files[_n_files] = fd;
        _n_files++;
    }
    return fd;
}

void closeall()
{
    for (int i = _n_files - 1; i >= 0; --i) {
        close(_opened_files[i]);
        _opened_files[i] = -1;
    }
    _n_files = 0;
}

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
    record_fs_stat();
    assert(do_fsck());
    for (int i = 0; i < N_FS; ++i) {
        int ret = umount2(basepaths[i], 0);
        if (ret != 0) {
            fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                    fslist[i], basepaths[i], errnoname(errno));
            has_failure = true;
        }
    }
    assert(!has_failure);
}

void __attribute__((constructor)) init()
{
    /* open and mmap the test f/s image as well as its heap memory */
    fsfd_ext4 = open("/dev/ram0", O_RDWR);
    assert(fsfd_ext4 >= 0);
    fsimg_ext4 = mmap(NULL, fsize(fsfd_ext4), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext4, 0);
    assert(fsimg_ext4 != MAP_FAILED);
    
    fsfd_ext2 = open("/dev/ram1", O_RDWR);
    assert(fsfd_ext2 >= 0);
    fsimg_ext2 = mmap(NULL, fsize(fsfd_ext2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext2, 0);
    assert(fsimg_ext2 != MAP_FAILED);
    
    fsfd_jffs2 = open("/dev/mtdblock0", O_RDWR);
    assert(fsfd_jffs2 >= 0);
    fsimg_jffs2 = mmap(NULL, fsize(fsfd_jffs2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_jffs2, 0);
    assert(fsimg_jffs2 != MAP_FAILED);
}

/* The procedure that resets run-time states
 * Currently we just close all opened files
 */
void cleanup()
{
    for (int i = 0; i < _n_files; ++i) {
        close(_opened_files[i]);
        _opened_files[i] = 0;
    }
    _n_files = 0;
    errno = 0;
}
