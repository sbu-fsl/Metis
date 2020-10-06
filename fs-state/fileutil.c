#include "fileutil.h"

int cur_pid;
char func[9];
struct timespec begin_time;

int _opened_files[MAX_OPENED_FILES];
int _n_files;
size_t count;

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
