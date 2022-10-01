#include "fileutil.h"
#include "cr.h"
#include "custom_heap.h"
#include <sys/wait.h>
#include <sys/vfs.h>

#define IS_CHECKPOINT true
#define IS_SNAPSHOT false

struct fs_stat *fsinfos;
int cur_pid;
char func[FUNC_NAME_LEN + 1];
struct timespec begin_time;
// Time spent since the program starts
struct timespec epoch;

int _opened_files[1024];
int _n_files;
size_t count;
absfs_set_t absfs_set;

#ifdef CBUF_IMAGE
circular_buf_sum_t *fsimg_bufs;
#endif

int compare_file_content(const char *path1, const char *path2)
{
    const size_t bs = 4096;
    char buf1[bs], buf2[bs];
    struct stat f1, f2;
    int fd1 = -1, fd2 = -1, ret = 0;
    /* Open the two files */
    fd1 = open(path1, O_RDONLY);
    if (fd1 < 0) {
        logerr("[seqid=%zu] cannot open %s", count, path1);
        return -1;
    }
    fd2 = open(path2, O_RDONLY);
    if (fd2 < 0) {
        logerr("[seqid=%zu] cannot open %s", count, path1);
        close(fd1);
        return -1;
    }
    /* Get file properties: Make sure equal file size */
    ret = fstat(fd1, &f1);
    if (ret) {
        logerr("[seqid=%zu] fstat '%s' failed", count, path1);
        ret = -1;
        goto end;
    }
    ret = fstat(fd2, &f2);
    if (ret) {
        logerr("[seqid=%zu] fstat '%s' failed", count, path2);
        ret = -1;
        goto end;
    }
    if (f1.st_size != f2.st_size) {
        logwarn("[seqid=%zu] '%s' and '%s' size differ. "
                "'%s' has %zu bytes and '%s' has %zu.", count,
                path1, path2, path1, f1.st_size, path2, f2.st_size);
        ret = 1;
        goto end;
    }
    /* Compare the file content */
    int r1 = 0, r2 = 0;
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
            logwarn("[seqid=%zu] content in '%s' and '%s' "
                    "is not equal.\n", count, path1, path2);
            ret = -1;
	    break;
        }
    }
    if (r1 < 0 || r2 < 0) {
        logerr("[seqid=%zu] error occurred when reading.", count);
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
        logwarn("[seqid=%zu] discrepancy in values found:", count);
        for (int i = 0; i < n_fs; ++i)
            logwarn("[%s]: %d", fses[i], nums[i]);
    }
    return res;
}

void dump_absfs(const char *basepath)
{
    absfs_t absfs;
    absfs.hash_option = absfs_hash_method;
    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, true, submit_error);
    destroy_abstract_fs(&absfs);
}

static void tell_absfs_hash_method()
{
    char *hashname;
    switch (absfs_hash_method) {
        case xxh128_t:
            hashname = "xxh3-128";
            break;

        case xxh3_t:
            hashname = "xxh3-64";
            break;

        case md5_t:
            hashname = "md5";
            break;

        case crc32_t:
            hashname = "crc32";
            break;

        default:
            hashname = "(unknown)";
            break;
    }
    fprintf(stderr, "Selected abstraction hash method is %s.\n", hashname);
}

bool compare_equality_absfs(char **fses, int n_fs, absfs_state_t *absfs)
{
    bool res = true;
    /* The macros are defined in include/abstract_fs.h */
    int retry_limit = SYSCALL_RETRY_LIMIT;
    absfs_state_t base;
retry:
    /* Calculate the abstract file system states */
    for (int i = 0; i < n_fs; ++i) {
        compute_abstract_state(get_basepaths()[i], absfs[i]);
    }
    /* New: record abstract states in the main log */
    static size_t prev_seqid = 0;
    if (prev_seqid != count) {
        char abs_state_str[33] = {0};
        char *strp = abs_state_str;
        for (int i = 0; i < 16; ++i) {
            // second arg of snprintf: count the null-terminator. However, the
    	    // return value does not include the terminator.
            size_t res = snprintf(strp, 3, "%02x", absfs[0][i]);
            strp += res;
        }
        makelog("absfs = {%s}\n", abs_state_str);
        prev_seqid = count;
    }
    /* Compare */
    memcpy(base, absfs[0], sizeof(absfs_state_t));
    for (int i = 1; i < n_fs; ++i) {
        if (memcmp(base, absfs[i], sizeof(absfs_state_t)) != 0) {
            res = false;
            break;
        }
    }
    if (!res && retry_limit <= 0) {
        logwarn("[seqid=%zu] Discrepancy in abstract states found:",
                count);
        for (int i = 0; i < n_fs; ++i) {
            logwarn("[seqid=%zu, fs=%s]: Directory structure:",
                    count, fses[i]);
            dump_absfs(get_basepaths()[i]);
            submit_error("hash=", count, fses[i]);
            print_abstract_fs_state(submit_error, absfs[i]);
            submit_error("\n");
        }
    } else if (!res && retry_limit > 0) {
        retry_limit--;
        res = true;
        logwarn("[seqid=%zu] Discrepancy in abstract states found:", count);
        for (int i = 0; i < n_fs; ++i) {
            submit_error("%s has the state ", fses[i]);
            print_abstract_fs_state(submit_error, absfs[i]);
            submit_error("\n");
        }
        logwarn("Retrying... The retry limit is %d.", retry_limit);
        usleep(5000);
        goto retry;
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
        logwarn("[%zu] Discrepancy in existence of files found:", count);
        for (int i = 0; i < n_fs; ++i) {
            logwarn("[%s]: %s: %d", fses[i], fpaths[i], fexists[i]);
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
            logwarn("[seqid=%zu] [%s] (%s) is different from [%s] "
                    "(%s)", count, fses[i-1], fpaths[i-1], fses[i],
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
            logerr("%s: cannot create folder %s (%s)\n", __func__,
                    folder, errnoname(errno));
            return -errno;
        }
    } else if (ret < 0) {
        logerr("%s: failed to stat %s, error is %s\n", __func__,
                folder, errnoname(errno));
        return -errno;
    } else {
        if (!S_ISDIR(st.st_mode)) {
            errno = ENOTDIR;
            logerr("%s: folder %s is not a directory.\n", __func__,
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
        logerr("cannot create file %s", outpath);
        return;
    }
    size_t remaining = fsize(fsfd);
    char *ptr = fsimg;
    while (remaining > 0) {
        size_t writelen = (remaining >= bs) ? bs : remaining;
        ssize_t writeres = write(dmpfd, ptr, writelen);
        if (writeres < 0) {
            logerr("cannot write data to image dump %s", outpath);
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
            logwarn("Cannot dump %s on %s, dd exited with %d.",
                    fsname, devname, WEXITSTATUS(status));
        }
    } else if (WIFSIGNALED(status)) {
        logwarn("Cannot dump %s on %s, dd was terminated by signal "
                "%d.", fsname, devname, WTERMSIG(status));
    } else {
        logwarn("Cannot dump %s on %s, dd has exit code %d.",
                fsname, devname, status);
    }
}

static void dump_fs_images(const char *folder)
{
    char fullpath[PATH_MAX] = {0};
    assert(ensure_dump_dir(folder) == 0);
    for (int i = 0; i < get_n_fs(); ++i) {
        /* Dump the mmap'ed object */
        snprintf(fullpath, PATH_MAX, "%s/%s-mmap-%zu.img", folder,
                 get_fslist()[i], count);
        dump_mmaped(fullpath, get_fsfds()[i], get_fsimgs()[i]);
        /* Dump the device by direct copying */
        dump_device(get_devlist()[i], folder, get_fslist()[i]);
    }
}

// Pass boolean or flag and only open/mmap for R or W, not both.
static void mmap_devices(bool ckpt)
{
    for (int i = 0; i < get_n_fs(); ++i) {
        if (!get_devlist()[i])
            continue;
        int fsfd = -1;
        if (ckpt) 
            fsfd = open(get_devlist()[i], O_RDONLY);
        else
            fsfd = open(get_devlist()[i], O_WRONLY);
        assert(fsfd >= 0);
        // Call fsize before, assert if size is <= 0
        ssize_t devsz = fsize(fsfd);
        assert(devsz > 0);
        // Use MAP_PRIVATE for Read/checkpoint 
        // But for Write/restore may need MAP_SHARED (but try MAP_PRIVATE)
        void *fsimg = MAP_FAILED;
        if (ckpt)
            fsimg = mmap(NULL, devsz, PROT_READ, MAP_PRIVATE, fsfd, 0);
        else
            fsimg = mmap(NULL, devsz, PROT_WRITE, MAP_SHARED, fsfd, 0);
        assert(fsimg != MAP_FAILED);
        get_fsfds()[i] = fsfd;
        get_fsimgs()[i] = fsimg;
    }
}

static void unmap_devices()
{
    int ret = -1;
    for (int i = 0; i < get_n_fs(); ++i) {
        if (!get_devlist()[i])
            continue;
        // Verify fsize returns > 0, assert if munmap failed
        ssize_t devsz = fsize(get_fsfds()[i]);
        assert(devsz > 0);

        ret = munmap(get_fsimgs()[i], devsz); 
        assert(ret == 0);
        // Assert if close() failed
        ret = close(get_fsfds()[i]); 
        assert(ret == 0);
    }
}

static void init_basepaths()
{
    /* Initialize base paths */
    printf("%d file systems to test.\n", get_n_fs());
    for (int i = 0; i < get_n_fs(); ++i) {
        size_t len = snprintf(NULL, 0, "/mnt/test-%s%s",
                              get_fslist()[i], get_fssuffix()[i]);
        get_basepaths()[i] = calloc(1, len + 1);
        snprintf(get_basepaths()[i], len + 1, "/mnt/test-%s%s",
                 get_fslist()[i], get_fssuffix()[i]);
    }
}

static int checkpoint_verifs(size_t key, const char *mp)
{
    int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0) {
        logerr("Cannot open mountpoint %s", mp);
        return errno;
    }

    int ret = ioctl(mpfd, VERIFS_CHECKPOINT, key);
    if (ret < 0) {
        logerr("Cannot perform checkpoint at %s", mp);
        ret = errno;
    }
    close(mpfd);
    return ret;
}

static int restore_verifs(size_t key, const char *mp)
{
    int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0) {
        logerr("Cannot open mountpoint %s", mp);
        return errno;
    }

    int ret = ioctl(mpfd, VERIFS_RESTORE, key);
    if (ret < 0) {
        logerr("Cannot perform restore at %s with key %zu", mp, key);
        ret = errno;
    }

    close(mpfd);
    return ret;
}

static size_t state_depth = 0;

/*
 *  Called before the spin's checkpoint of concrete state
 */
static long checkpoint_before_hook(unsigned char *ptr)
{
    submit_seq("checkpoint\n");
    makelog("[seqid = %d] checkpoint (%zu)\n", count, state_depth);

    mmap_devices(IS_CHECKPOINT);

#ifdef CBUF_IMAGE
    for (int i = 0; i < get_n_fs(); ++i) {
        insert_circular_buf(fsimg_bufs, i, get_devsize_kb()[i], get_fsimgs()[i],
            state_depth, count, IS_CHECKPOINT);
    }
#endif

    state_depth++;

    for (int i = 0; i < get_n_fs(); ++i) {
        if (!is_verifs(get_fslist()[i]))
            continue;
        int res = checkpoint_verifs(state_depth, get_basepaths()[i]); 
        if (res != 0) {
            logerr("Failed to checkpoint a verifiable file system %s.",
                   get_fslist()[i]);
        }
    }

    return 0;
}

/*
 *  Called after the spin's checkpoint of concrete state
 */
static long checkpoint_after_hook(unsigned char *ptr)
{
    unmap_devices();
    // assert(do_fsck());
    // dump_fs_images("snapshots");
    return 0;
}

/*
 *  Called before the spin's restore of concrete state
 */
static long restore_before_hook(unsigned char *ptr)
{
    state_depth--;
    
    submit_seq("restore\n");
    makelog("[seqid = %d] restore (%zu)\n", count, state_depth);

    mmap_devices(IS_SNAPSHOT);

    for (int i = 0; i < get_n_fs(); ++i) {
        if (!is_verifs(get_fslist()[i]))
            continue;
        int res = restore_verifs(state_depth, get_basepaths()[i]);
        if (res != 0) {
            logerr("Failed to restore a verifiable file system %s.",
                    get_fslist()[i]);
        }
    }

    // assert(do_fsck());
    return 0;
}

/*
 *  Called after the spin's restore of concrete state
 */
static long restore_after_hook(unsigned char *ptr)
{
    unmap_devices();
    // assert(do_fsck());
    // dump_fs_images("after-restore");
    return 0;
}

/*
 *  Called before the spin's checkpoint of abstract state
 */
static long update_before_hook(unsigned char *ptr)
{
    absfs_set_add(absfs_set, get_absfs());
    return 0;
}

/*
 *  Called after the spin's checkpoint of abstract state
 */
static long update_after_hook(unsigned char *ptr)
{
    return 0;
}

/*
 *  Called before the spin's restore of abstract state
 */
static long revert_before_hook(unsigned char *ptr)
{
    return 0;
}

/*
 *  Called after the spin's restore of abstract state
 */
static long revert_after_hook(unsigned char *ptr)
{
    return 0;
}

extern long (*c_stack_before)(unsigned char *);
extern long (*c_stack_after)(unsigned char *);
extern long (*c_unstack_before)(unsigned char *);
extern long (*c_unstack_after)(unsigned char *);
extern long (*c_update_before)(unsigned char *);
extern long (*c_update_after)(unsigned char *);
extern long (*c_revert_before)(unsigned char *);
extern long (*c_revert_after)(unsigned char *);

static void equalize_free_spaces(void)
{
    size_t free_spaces[MAX_FS] = {0};
    size_t min_space = ULONG_MAX;
    const char *dummy_file = ".mcfs_dummy";
    mountall();
    /* Find free space of each file system being checked */
    for (int i = 0; i < get_n_fs(); ++i) {
        if (is_verifs(get_fslist()[i]))
            continue;
        struct statfs fsinfo;
        int ret = statfs(get_basepaths()[i], &fsinfo);
        if (ret != 0) {
            logerr("cannot statfs %s", get_basepaths()[i]);
            exit(1);
        }
        size_t free_spc = fsinfo.f_bfree * fsinfo.f_bsize;
        if (free_spc < min_space)
            min_space = free_spc;
        free_spaces[i] = free_spc;
    }
    /* Fill data to file systems who have greater than min_space of free space,
     * so that all file systems will have equal free capacities. */
    for (int i = 0; i < get_n_fs(); ++i) {
        if (is_verifs(get_fslist()[i]))
            continue;
        size_t fillsz = free_spaces[i] - min_space;
        char fullpath[PATH_MAX] = {0};
        snprintf(fullpath, PATH_MAX, "%s/%s", get_basepaths()[i], dummy_file);
        /* Create/open the dummy file */
        int fd = open(fullpath, O_CREAT | O_TRUNC | O_RDWR, 0666);
        if (fd < 0) {
            logerr("cannot open %s", fullpath);
            exit(1);
        }
        /* Start filling */
        memset(fullpath, 0, PATH_MAX);
        while (fillsz > 0) {
            size_t writesz = min(fillsz, PATH_MAX);
            ssize_t ret = write(fd, fullpath, writesz);
            if (ret < 0) {
                logerr("cannot write data in %s", get_basepaths()[i]);
                exit(1);
            }
            fillsz -= ret;
        }
        close(fd);
    }
    unmount_all_strict();
}

extern void (*spin_after_argparse)(int argc, char **argv);
static void main_hook(int argc, char **argv)
{
    tell_absfs_hash_method();
    /* Fill initial abstract states */
    for (int i = 0; i < get_n_fs(); ++i) {
        compute_abstract_state(get_basepaths()[i], get_absfs()[i]);
    }
}

void __attribute__((constructor)) init()
{
    fsinfos = calloc(get_n_fs(), sizeof(struct fs_stat));
    if (!fsinfos)
        mem_alloc_err();
    char output_log_name[NAME_MAX] = {0};
    char error_log_name[NAME_MAX] = {0};
    char seq_log_name[NAME_MAX] = {0};
    char progname[NAME_MAX] = {0};
    ssize_t progname_len;
    try_init_myheap();
    init_basepaths();
    setup_filesystems();

    /* Initialize log daemon */
    // setvbuf(stdout, NULL, _IONBF, 0);
    // setvbuf(stderr, NULL, _IONBF, 0);

    progname_len = get_progname(progname);
    if (progname_len < 0) {
        fprintf(stderr, "Cannot get cmdline and program name: (%s:%ld)\n",
                errnoname(-progname_len), progname_len);
        exit(1);
    }

    add_ts_to_logname(output_log_name, NAME_MAX, OUTPUT_PREFIX, progname, "");
    add_ts_to_logname(error_log_name, NAME_MAX, ERROR_PREFIX, progname, "");
    add_ts_to_logname(seq_log_name, NAME_MAX, SEQ_PREFIX, progname, "");
    init_log_daemon(output_log_name, error_log_name, seq_log_name);

    /* Register hooks */
    c_stack_before = checkpoint_before_hook;
    c_stack_after = checkpoint_after_hook;
    c_unstack_before = restore_before_hook;
    c_unstack_after = restore_after_hook;
    c_update_before = update_before_hook;
    c_update_after = update_after_hook;
    c_revert_before = revert_before_hook;
    c_revert_after = revert_after_hook;
    spin_after_argparse = main_hook;

    /* Initialize absfs-set used for counting unique states */
    absfs_set_init(&absfs_set);

    /* Fill dummy data so that all file systems have the same amount of free
     * space (Only for non-VeriFS experiments, because currently VeriFS1 doesn't
     * have support for statvfs() yet) */
    equalize_free_spaces();
#ifdef CBUF_IMAGE
    circular_buf_init(&fsimg_bufs, get_n_fs(), get_devsize_kb());
#endif
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) cleanup()
{
    if (fsinfos)
        free(fsinfos);
    fflush(stdout);
    fflush(stderr);
    unset_myheap();
    destroy_log_daemon();
    // unfreeze_all();
#ifdef CBUF_IMAGE
    cleanup_cir_bufs(fsimg_bufs);
#endif
}
