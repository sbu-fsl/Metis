#include "fileutil.h"
#include "cr.h"
#include "custom_heap.h"
#include <sys/wait.h>
#include <sys/vfs.h>

int cur_pid;
char func[FUNC_NAME_LEN + 1];
struct timespec begin_time;
// Time spent since the program starts
struct timespec epoch;

int _opened_files[1024];
int _n_files;
size_t count;
absfs_set_t absfs_set;

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
    int r1, r2;
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
        logwarn("[seqid=%zu] discrepancy in values found:", count);
        for (int i = 0; i < n_fs; ++i)
            logwarn("[%s]: %d", fses[i], nums[i]);
    }
    return res;
}

void dump_absfs(const char *basepath)
{
    absfs_t absfs;
    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, true, submit_error);
}

bool compare_equality_absfs(const char **fses, int n_fs, absfs_state_t *absfs)
{
    bool res = true;
    /* The macros are defined in include/abstract_fs.h */
    int retry_limit = SYSCALL_RETRY_LIMIT;
    absfs_state_t base;
retry:
    /* Calculate the abstract file system states */
    for (int i = 0; i < n_fs; ++i) {
        compute_abstract_state(basepaths[i], absfs[i]);
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
            dump_absfs(basepaths[i]);
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
        logwarn("[%zu] Discrepancy in existence of files found:", count);
        for (int i = 0; i < n_fs; ++i) {
            logwarn("[%s]: %s: %d", fses[i], fpaths[i], fexists[i]);
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
        if (!devlist[i])
            continue;
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
        if (!devlist[i])
            continue;
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

static int checkpoint_zfs(size_t key, const char *mp)
{
    errno = 0;    
    int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0) {
        logerr("Cannot open mountpoint %s", mp);
        return errno;
    }

    char cmd[ARG_MAX] = {0};


    snprintf(cmd, ARG_MAX, "sudo ./sstest.sh c %zu", key);
 
    int ret = system(cmd);
    
    if (ret == -1 || WEXITSTATUS(ret) != 0){
        char buf[BUFSIZ];
        setbuf(stderr, buf);

        logerr("Cannot perform checkpoint at %s", mp);
        ret = errno;
    }
    /*
    snprintf(cmd, ARG_MAX, "zfs snapshot mcfszpool/fs1@testsnap%zu", key);
    int ret = system(cmd);
    
    if (ret == -1 || WEXITSTATUS(ret) != 0){
        char buf[BUFSIZ];
        setbuf(stderr, buf);

        logerr("Cannot perform checkpoint at %s", mp);
        ret = errno;
    }
   
    //incremental send. If it fails, send onlt the top one.
    //snprintf(cmd, ARG_MAX, "ss1=$(zfs list -t snapshot -o name | grep mcfszpool/fs1@testsnap | tac | tail -n +2); ss2=$(zfs list -t snapshot -o name | grep zpooltest/fs1@testsnap | tac | tail -n +1); sudo zfs send -i $ss1 $ss2 | sudo  zfs recv zpooltest/fs > incrementalsend_err_file");
   
    snprintf(cmd, ARG_MAX, "key=%zu; sudo zfs snapshot mcfszpool/fs1@testsnap$key; ss1=$(zfs list -t snapshot -o name | grep mcfszpool/fs1@testsnap | tac | tail -n +2); if [ "$ss1" != "" ]; then sudo zfs send -i $ss1 mcfszpool/fs1@testsnap$key | sudo  zfs recv zpooltest/fs;  else  sudo zfs send mcfszpool/fs1@testsnap$key | sudo  zfs recv zpooltest/fs; fi  if [ "$ss1" != "" ]; then  sudo zfs destroy $ss1  fi  ", key);   

    logerr("zfs incremental send command is %s", cmd);
    //snprintf(cmd, ARG_MAX, "zfs send ", key);
    ret = system(cmd);

    if (ret == -1 || WEXITSTATUS(ret) != 0){
        char buf[BUFSIZ];
        setbuf(stderr, buf);
        logerr("Cannot perform checkpoint at %s", mp);
        ret = errno;
    }

    close(mpfd);
    */
    //sleep(3);
    return ret;
}

static int restore_zfs(size_t key, const char *mp)
{
    errno = 0;
    int mpfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (mpfd < 0) {
        logerr("Cannot open mountpoint %s", mp);
        return errno;
    }
    char cmd[ARG_MAX] = {0};
    
    snprintf(cmd, ARG_MAX, "sudo ./sstest.sh r %zu", key);
 
    int ret = system(cmd);
    
    if (ret == -1 || WEXITSTATUS(ret) != 0){
        char buf[BUFSIZ];
        setbuf(stderr, buf);

        logerr("Cannot perform checkpoint at %s", mp);
        ret = errno;
    }
    /*
    snprintf(cmd, ARG_MAX, "zfs rollback -r mcfszpool/fs1@testsnap%zu", key);
    int ret = system(cmd);
    if (ret  == -1 || WEXITSTATUS(ret) != 0){
        logerr("Cannot perform restore at %s with key %zu", mp, key);
        ret = errno;
    }
    
    snprintf(cmd, ARG_MAX, "zfs destroy mcfszpool/fs1@testsnap%zu", key);
    ret = system(cmd);
    if (ret  == -1 || WEXITSTATUS(ret) != 0){
        logerr("Cannot perform restore at %s with key %zu", mp, key);
        ret = errno;
    }
    */
    close(mpfd);
    //sleep(3);
    return ret;
}



static int checkpoint_verifs(size_t key, const char *mp)
{
    errno = 0;
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

static long checkpoint_before_hook(unsigned char *ptr)
{
    mmap_devices();
    return 0;
}

static long checkpoint_after_hook(unsigned char *ptr)
{
    unmap_devices();
    // assert(do_fsck());
    // dump_fs_images("snapshots");
    return 0;
}

static long restore_before_hook(unsigned char *ptr)
{
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

static size_t state_depth = 0;
static long update_before_hook(unsigned char *ptr)
{
    submit_seq("checkpoint\n");
    makelog("[seqid = %d] checkpoint (%zu)\n", count, state_depth);
    absfs_set_add(absfs_set, absfs);
    state_depth++;
    for (int i = 0; i < N_FS; ++i) {
        if (!is_verifs(fslist[i]) && fslist[i] != "zfs"){
            continue;
	}


	int res = 0;
	if( is_verifs(fslist[i]) ){
        	res = checkpoint_verifs(state_depth, basepaths[i]); 
	}
	else if( fslist[i] == "zfs"){
		res = checkpoint_zfs(state_depth, basepaths[i]);
	}

        if (res != 0) {
            logerr("Failed to checkpoint a verifiable file system %s.",
                   fslist[i]);
        }
    }
    return 0;
}

static long update_after_hook(unsigned char *ptr)
{
    return 0;
}

static long revert_before_hook(unsigned char *ptr)
{
    submit_seq("restore\n");
    makelog("[seqid = %d] restore (%p)\n", count, state_depth);
    for (int i = 0; i < N_FS; ++i) {
        if (!is_verifs(fslist[i]) && fslist[i] != "zfs")
            continue;

	int res = 0;
	if ( is_verifs(fslist[i]) )
	        res = restore_verifs(state_depth, basepaths[i]);
	else if (fslist[i] == "zfs" )
		res = restore_zfs(state_depth, basepaths[i]);
        if (res != 0) {
            logerr("Failed to restore a verifiable file system %s.",
                    fslist[i]);
        }
    }
    state_depth--;
    return 0;
}

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
    size_t free_spaces[N_FS] = {0};
    size_t min_space = ULONG_MAX;
    const char *dummy_file = ".mcfs_dummy";
    mountall();
    /* Find free space of each file system being checked */
    for (int i = 0; i < N_FS; ++i) {
        if (is_verifs(fslist[i]) )
            continue;
        struct statfs fsinfo;
        int ret = statfs(basepaths[i], &fsinfo);
        if (ret != 0) {
            logerr("cannot statfs %s", basepaths[i]);
            exit(1);
        }
        size_t free_spc = fsinfo.f_bfree * fsinfo.f_bsize;
        if (free_spc < min_space)
            min_space = free_spc;
        free_spaces[i] = free_spc;
    }
    /* Fill data to file systems who have greater than min_space of free space,
     * so that all file systems will have equal free capacities. */
    for (int i = 0; i < N_FS; ++i) {
        if (is_verifs(fslist[i]) )
            continue;
        size_t fillsz = free_spaces[i] - min_space;
        char fullpath[PATH_MAX] = {0};
        snprintf(fullpath, PATH_MAX, "%s/%s", basepaths[i], dummy_file);
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
                logerr("cannot write data in %s", basepaths[i]);
                exit(1);
            }
            fillsz -= ret;
        }
        close(fd);
    }
    unmount_all();
}

void __attribute__((constructor)) init()
{
    try_init_myheap();
    init_basepaths();
    /* Fill initial abstract states */
    for (int i = 0; i < N_FS; ++i) {
        compute_abstract_state(basepaths[i], absfs[i]);
    }
    
    /* Initialize log daemon */
    // setvbuf(stdout, NULL, _IONBF, 0);
    // setvbuf(stderr, NULL, _IONBF, 0);

    init_log_daemon(OUTPUT_LOG_PATH, ERROR_LOG_PATH, SEQ_LOG_PATH);
    

    /* Register hooks */
    c_stack_before = checkpoint_before_hook;
    c_stack_after = checkpoint_after_hook;
    c_unstack_before = restore_before_hook;
    c_unstack_after = restore_after_hook;
    c_update_before = update_before_hook;
    c_update_after = update_after_hook;
    c_revert_before = revert_before_hook;
    c_revert_after = revert_after_hook;

    /* Initialize absfs-set used for counting unique states */
    absfs_set_init(&absfs_set);

    /* Fill dummy data so that all file systems have the same amount of free
     * space (Only for non-VeriFS experiments, because currently VeriFS1 doesn't
     * have support for statvfs() yet) */
    equalize_free_spaces();
}

/*
 * This cleanup procedure will be called when the program exits.
 */
void __attribute__((destructor)) cleanup()
{
    fflush(stdout);
    fflush(stderr);
    unset_myheap();
    destroy_log_daemon();
    // unfreeze_all();
}
