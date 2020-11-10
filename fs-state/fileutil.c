#include "fileutil.h"

#define __USE_XOPEN_EXTENDED 1
#include <ftw.h>
#include <sys/vfs.h>

int cur_pid;
char func[9];
struct timespec begin_time;

struct fs_opened_files opened_files[N_FS];
int _opened_files[1024];
int _n_files;
size_t count;
char* devlist[] = {"/dev/ram0", "/dev/ram1" };

int compare_file_content(int fd1, int fd2)
{
    const size_t bs = 4096;
    char buf1[bs], buf2[bs];
    struct stat f1, f2;
    int ret = 0;
    /* Get file properties: Make sure equal file size */
    ret = fstat(fd1, &f1);
    if (ret) {
        fprintf(stderr, "[%d] cmp_file_content: fstat f1 failed (%d)\n",
                cur_pid, errno);
        return -1;
    }
    ret = fstat(fd2, &f2);
    if (ret) {
        fprintf(stderr, "[%d] cmp_file_content: fstat f2 failed (%d)\n",
                cur_pid, errno);
        return -1;
    }
    if (f1.st_size != f2.st_size) {
        fprintf(stderr, "[%d] cmp_file_content: f1 and f2 size differ. "
                "f1 has %zu bytes and f2 has %zu.\n", cur_pid,
                f1.st_size, f2.st_size);
        return 1;
    }
    /* Compare the file content */
    int r1, r2;
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
		fprintf(stderr, "[%d] cmp_file_content: "
			"f1 and f2 content is not equal.\n", cur_pid);
            return 1;
        }
    }
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    if (r1 < 0 || r2 < 0) {
	    fprintf(stderr, "[%d] cmp_file_content: "
		    "error occurred when reading: %d\n", cur_pid, errno);
    }
    return 0;
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
        fprintf(stderr, "[%d] Discrepancy in values found:\n", cur_pid);
        for (int i = 0; i < n_fs; ++i)
            fprintf(stderr, "[%d] [%s]: %d\n", cur_pid, fses[i], nums[i]);
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
        fprintf(stderr,
		"[seqid=%zu] Discrepancy in abstract states found:\n", count);
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
        fprintf(stderr, "[%d] Discrepancy in existence of files found:\n",
		cur_pid);
        for (int i = 0; i < n_fs; ++i) {
            fprintf(stderr, "[%d] [%s]: %s: %d\n", cur_pid, fses[i], fpaths[i],
                    fexists[i]);
        }
    }
    return res;
}

bool is_all_fd_invalid(int *fds, int n_fs)
{
    bool res = true;
    for (int i = 0; i < n_fs; ++i) {
        errno = 0;
        /* Stop if any of the fd is valid */
        if (fcntl(fds[i], F_GETFD) != -1) {
            res = false;
            break;
        }
    }
    return res;
}

bool compare_equality_fcontent(char **fses, int n_fs, char **fpaths, int *fds)
{
    bool res = true;

    if (!compare_equality_fexists(fses, n_fs, fpaths))
        return false;

    /* If none of the files exists, return TRUE */
    if (check_file_existence(fpaths[0]) == false)
        return true;

    /* If all fds are not valid, return TRUE */
    if (is_all_fd_invalid(fds, n_fs))
        return true;

    for (int i = 1; i < n_fs; ++i) {
        if (compare_file_content(fds[i-1], fds[i]) != 0) {
            if (res)
                res = false;
            fprintf(stderr, "[%d] [%s] (%s) is different from [%s] (%s)\n",
                    cur_pid, fses[i-1], fpaths[i-1], fses[i], fpaths[i]);
        }
    }
    return res;
}

static int _file_count;
int on_each_file(const char *fpath, const struct stat *sb,
		 int typeflag, struct FTW *ftwbuf)
{
	struct stat stbf;
	int ret = stat(fpath, &stbf);
	if (ret != 0) {
		fprintf(stderr, "cannot stat %s: %s\n", fpath, errnoname(errno));
		return ret;
	}
	_file_count++;
	return 0;
}

/* Walk the file system and count how many files there are.
 * If the file system is corrupted in a way where an existing dentry does not
 * have its corresponding inode, this will return -1
 */
static int how_many_files(const char *mountpoint)
{
	_file_count = 0;
	int ret = nftw(mountpoint, on_each_file, 16, FTW_PHYS);
    if (ret != 0) {
        fprintf(stderr, "nftw failed, returned %d, errno = %s\n",
                ret, errnoname(errno));
    }
	return (ret == 0) ? _file_count : -1;
}

static int try_create_testdir(const char *mp, const char *name)
{
    char dirpath[PATH_MAX] = {0};
    snprintf(dirpath, PATH_MAX, "%s/%s", mp, name);
    int ret = mkdir(dirpath, 0755);
    if (ret != 0)
        ret = errno;
    rmdir(dirpath);
    return ret;
}

static bool check_capacity(const char *mountpoint)
{
    struct statfs st;
    int ret = statfs(mountpoint, &st);
    if (ret < 0) {
        fprintf(stderr, "Cannot stat file system %s: %d\n", mountpoint, errno);
        return false;
    }
    /* Try make a directory if statfs says there's free space or the file system
     * is empty */
    char dirpath[PATH_MAX] = {0};
    if (st.f_bfree > 0) {
        ret = try_create_testdir(mountpoint, "__testdir");
        if (ret != 0) {
            fprintf(stderr, "There is free space but mkdir returns %s.\n",
                    errnoname(ret));
            if (ret == ENOSPC)
                return false;
        }
    } else if (_file_count <= 0) {
        ret = try_create_testdir(mountpoint, "__testdir2");
        if (ret != 0) {
            fprintf(stderr, "File system is empty but mkdir returns %s.\n",
                    errnoname(ret));
            if (ret == ENOSPC)
                return false;
        }
    }
    return true;
}

bool filesystems_are_good()
{
    bool result = true;
    if (ABORT_ON_BADFS == 0)
        return result;
    for (int i = 0; i < N_FS; ++i) {
        int ret = how_many_files(basepaths[i]);
        if (ret < 0) { 
            fprintf(stderr, "File system <%s> at %s is corrupted due to "
                    "a dangling dentry without corresponding inode.\n",
                    fslist[i], basepaths[i]);
            result = false;
            continue;
        }
        bool ret2 = check_capacity(basepaths[i]);
        if (!ret2) {
            fprintf(stderr, "File system <%s> at %s is corrupted because "
                    "it falsely claims no-space error.\n", fslist[i],
                    basepaths[i]);
            result = false;
            continue;
        }
    }
    return result;
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

void mountall()
{
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
    reopen_all_opened_files();
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
    // close all opened fds before unmounting
    close_all_opened_fds();
    bool has_failure = false;
    for (int i = 0; i < N_FS; ++i) {
        int ret = umount2(basepaths[i], MNT_FORCE);
        if (ret != 0) {
            fprintf(stderr, "Could not unmount file system %s at %s (%s)\n",
                    fslist[i], basepaths[i], errnoname(errno));
            has_failure = true;
        }
    }
    assert(!has_failure);
}

void init_opened_files_state() {
    for(int i = 0; i < N_FS; i++) {
        opened_files[i].count = -1;
    }
}	
struct FileState create_file_state(char* path, int flag, int fd) {
    struct FileState fs;
    strcpy(fs._path, path);
    fs._isOpen = 1;
    fs._flag = flag;
    fs._fd = fd;
    fs._pos = 0;
    return fs;
}

void print_file_state(struct FileState fs){
    printf("Path : %s isOpen : %d flag : %d fd : %d _pos : %d", fs._path, fs._isOpen, fs._flag, fs._fd, fs._pos);
}

int my_open(int n_fs, char* path, int flag, int permission){
    int fd = open(path, flag);
    if(fd<0)
	return -1;
    struct FileState fs = create_file_state(path, flag, fd);
    struct fs_opened_files fs_open_state = opened_files[n_fs]; 
    print_file_state(fs);
    if(fs_open_state.count < MAX_FILES-1) {
        fs_open_state.files[++fs_open_state.count] = fs;
    } else {
        printf("Cannot open file: %s. Reached max number of files\n", path);
	return -1;
    }
    opened_files[n_fs] = fs_open_state;
    return fd;
}

int find_idx(struct fs_opened_files fs_open_state, char* path) {
    for (int i = 0; i <= fs_open_state.count; i++) {
        if (strcmp(fs_open_state.files[i]._path, path) == 0) {
            return i;
        }
    }
    return -1;
}

int my_lseek(int n_fs, char* path, off_t offset, int whence) {
    // find the state of this file
    struct fs_opened_files fs_open_state = opened_files[n_fs];
    int idx = find_idx(fs_open_state, path);
    int fd = -1, curr_pos = 0;
    if (idx == -1) {
        printf("File %s not in opened state\n", path);
	return -1;
    } else {
        fd = fs_open_state.files[idx]._fd;
        curr_pos = fs_open_state.files[idx]._pos;
    }
    lseek(fd, curr_pos + offset, whence);
    
    // update the current seek position of the opened file.
    fs_open_state.files[idx]._pos = lseek(fs_open_state.files[idx]._fd, 0, SEEK_CUR);
    print_file_state(fs_open_state.files[idx]);
    opened_files[n_fs] = fs_open_state;
    return 0;
}

void my_close(int n_fs, char* path) {
    struct fs_opened_files fs_open_state = opened_files[n_fs];
    int idx = find_idx(fs_open_state, path);
    if (idx != -1) {
        close(fs_open_state.files[idx]._fd);
	for(int i = idx; i <= fs_open_state.count; i++) {
            fs_open_state.files[i] = fs_open_state.files[i+1];
	}
	fs_open_state.count--;
    }
    opened_files[n_fs] = fs_open_state;
}

void reopen_all_opened_files() {
    for(int i = 0; i < N_FS; i++) {
        for(int j = 0; j <= opened_files[i].count; j++) {
            /*
	     * all opened files' descriptors were closed before unmount. Hence after remount, reinitialize all the
	     * descriptors with open() call.
	     *
	     * TODO: Find if there is a way to restore the file descriptors across mounts.
	     */
            opened_files[i].files[j]._fd = open(opened_files[i].files[j]._path, opened_files[i].files[j]._flag);
	    opened_files[i].files[j]._isOpen = 1;
        }
    }
}

void close_all_opened_fds() {
    for(int i = 0; i < N_FS; i++) {
        for(int j = 0; j <= opened_files[i].count; j++) {
            close(opened_files[i].files[j]._fd);
            opened_files[i].files[j]._isOpen = 0;
        }
    }
}

void close_all_opened_files() {
    for(int i = 0; i < N_FS; i++) {
        for(int j = 0; j <= opened_files[i].count; j++) {
            close(opened_files[i].files[j]._fd);
            //opened_files[i].files[j]._isOpen = 0;
        }
	opened_files[i].count = -1;
    }
}

void __attribute__((constructor)) init()
{
   // fsfd_jffs2 = open("/dev/mtdblock0", O_RDWR);
   // assert(fsfd_jffs2 >= 0);
   // fsimg_jffs2 = mmap(NULL, fsize(fsfd_jffs2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_jffs2, 0);
   // assert(fsimg_jffs2 != MAP_FAILED);
   // 
   // fsfd_xfs = open("/dev/ram0", O_RDWR);
   // assert(fsfd_xfs >= 0);
   // fsimg_xfs = mmap(NULL, fsize(fsfd_xfs), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_xfs, 0);
   // assert(fsimg_xfs != MAP_FAILED);
    fsfd_ext2 = open("/dev/ram0", O_RDWR);
    assert(fsfd_ext2 >= 0);
    fsimg_ext2 = mmap(NULL, fsize(fsfd_ext2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext2, 0);
    assert(fsimg_ext2 != MAP_FAILED);

    fsfd_ext4 = open("/dev/ram1", O_RDWR);
    assert(fsfd_ext4 >= 0);
    fsimg_ext4 = mmap(NULL, fsize(fsfd_ext4), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext4, 0);
    assert(fsimg_ext4 != MAP_FAILED);
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
