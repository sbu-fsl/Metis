#include "fileutil.h"
#include <sys/wait.h>

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

bool compare_equality_values(const char **fses, int n_fs, int *nums)
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

bool compare_equality_absfs(const char **fses, int n_fs, absfs_state_t *absfs)
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

bool compare_equality_fexists(const char **fses, int n_fs, char **fpaths)
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

bool compare_equality_fcontent(const char **fses, int n_fs, char **fpaths)
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

static int ensure_dump_dir(const char *folder)
{
    struct stat st;
    int ret = stat(folder, &st);
    /* Try creating the folder if it doesn't exist */
    if (ret < 0 && errno == ENOENT) {
        ret = mkdir(folder, 0755);
        if (ret < 0) {
            fprintf(stderr, "%s: cannot create folder %s (%s)\n", __func__,
                    folder, errnoname(errno));
            return -errno;
        }
    } else if (ret < 0) {
        fprintf(stderr, "%s: failed to stat %s, error is %s\n", __func__,
                folder, errnoname(errno));
        return -errno;
    } else {
        if (!S_ISDIR(st.st_mode)) {
            fprintf(stderr, "%s: folder %s is not a directory.\n", __func__,
                    folder);
            return -ENOTDIR;
        }
    }
    return 0;
}

static void dump_mmaped(const char *outpath, int fsfd, void *fsimg)
{
    const size_t bs = 4096;
    int dmpfd = open(outpath, O_CREAT | O_RDWR | O_TRUNC, 0666);
    if (dmpfd < 0) {
        fprintf(stderr, "%s: cannot create file %s (%s)\n", __func__,
                outpath, errnoname(errno));
        return;
    }
    size_t remaining = fsize(fsfd);
    char *ptr = fsimg;
    while (remaining > 0) {
        size_t writelen = (remaining >= bs) ? bs : remaining;
        ssize_t writeres = write(dmpfd, ptr, writelen);
        if (writeres < 0) {
            fprintf(stderr, "%s: cannot write data to image dump %s (%s)\n",
                    __func__, outpath, errnoname(errno));
            close(dmpfd);
            break;
        }
        ptr += writeres;
        remaining -= writeres;
    }
    close(dmpfd);
}

static void dump_device(const char *devname, const char *folder,
        const char *fsname)
{
    char cmd[ARG_MAX] = {0};
    snprintf(cmd, ARG_MAX, "dd if=%s of=%s/%s-dev-%zu.img bs=4k status=none",
             devname, folder, fsname, count);
    int status = system(cmd);
    if (WIFEXITED(status)) {
        if (WEXITSTATUS(status) != 0) {
            fprintf(stderr, "%s: Cannot dump %s on %s, dd exited with %d.\n",
                    __func__, fsname, devname, WEXITSTATUS(status));
        }
    } else if (WIFSIGNALED(status)) {
        fprintf(stderr, "%s: Cannot dump %s on %s, dd was terminated by signal "
                "%d.\n", __func__, fsname, devname, WTERMSIG(status));
    } else {
        fprintf(stderr, "%s: Cannot dump %s on %s, dd has exit code %d.\n",
                __func__, fsname, devname, status);
    }
}

static void dump_fs_images(const char *folder)
{
    char fullpath[PATH_MAX] = {0};
    assert(ensure_dump_dir(folder) == 0);
    for (int i = 0; i < N_FS; ++i) {
        /* Dump the mmap'ed object */
        snprintf(fullpath, PATH_MAX, "%s/%s-mmap-%zu.img", folder,
                 fslist[i], count);
        dump_mmaped(fullpath, fsfds[i], fsimgs[i]);
        /* Dump the device by direct copying */
        dump_device(devlist[i], folder, fslist[i]);
    }
}

static void mmap_devices()
{
    for (int i = 0; i < N_FS; ++i) {
        int fsfd = open(devlist[i], O_RDWR);
        assert(fsfd >= 0);
        void *fsimg = mmap(NULL, fsize(fsfd), PROT_READ | PROT_WRITE,
                MAP_SHARED, fsfd, 0);
        assert(fsimg != MAP_FAILED);
        fsfds[i] = fsfd;
        fsimgs[i] = fsimg;
    }
}

static void unmap_devices()
{
    for (int i = 0; i < N_FS; ++i) {
        munmap(fsimgs[i], fsize(fsfds[i]));
        close(fsfds[i]);
    }
}

static void init_basepaths()
{
    /* Initialize base paths */
    printf("%ld file systems to test.\n", N_FS);
    for (int i = 0; i < N_FS; ++i) {
        size_t len = snprintf(NULL, 0, "/mnt/test-%s", fslist[i]);
        basepaths[i] = calloc(1, len + 1);
        snprintf(basepaths[i], len + 1, "/mnt/test-%s", fslist[i]);
    }
}

static long checkpoint_before_hook(unsigned char *ptr)
{
    fprintf(seqfp, "checkpoint\n");
    makelog("[seqid = %d] checkpoint\n", count);
    mmap_devices();
    // assert(do_fsck());
    return 0;
}

static long checkpoint_after_hook(unsigned char *ptr)
{
    unmap_devices();
    assert(do_fsck());
    // dump_fs_images("snapshots");
    return 0;
}

static long restore_before_hook(unsigned char *ptr)
{
    fprintf(seqfp, "restore\n");
    makelog("[seqid = %d] restore\n", count);
    mmap_devices();
    // assert(do_fsck());
    return 0;
}

static long restore_after_hook(unsigned char *ptr)
{
    unmap_devices();
    // assert(do_fsck());
    // dump_fs_images("after-restore");
    return 0;
}

extern long (*c_stack_before)(unsigned char *);
extern long (*c_stack_after)(unsigned char *);
extern long (*c_unstack_before)(unsigned char *);
extern long (*c_unstack_after)(unsigned char *);

void __attribute__((constructor)) init()
{
    init_basepaths();
    /* Clear all excluded dirs/files */
    clear_excluded_files();
    /* Fill initial abstract states */
    for (int i = 0; i < N_FS; ++i) {
        compute_abstract_state(basepaths[i], absfs[i]);
    }
    /* open sequence file */
    seqfp = fopen("sequence.log", "w");
    assert(seqfp);

    /* Register hooks */
    c_stack_before = checkpoint_before_hook;
    c_stack_after = checkpoint_after_hook;
    c_unstack_before = restore_before_hook;
    c_unstack_after = restore_after_hook;
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) cleanup()
{
    fflush(stdout);
    fflush(stderr);
    fclose(seqfp);
    unfreeze_all();
}
