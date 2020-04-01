c_code {
\#include "fileutil.h"

const char *filename = "test.txt";
const char *dirname = "testdir";
/* Reference f/s: tmpfs */
const char *rfs_path = "/tmp/test";
/* Target f/s */
const char *tfs_path = "/mnt/shared/test";

int r1, r2, err1, err2;
int fd1 = -1, fd2 = -1;
char *rfs_file, *rfs_dir, *tfs_file, *tfs_dir;
bool equality_of_existence, equality_of_content;

};

c_track "func" "9";
c_track "&errno" "sizeof(int)";

proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: d_step { 
        /* mkdir, check: retval, errno, existence */
        c_code {
            makecall(r1, err1, "%s, %o", mkdir, rfs_dir, 0755);
            makecall(r2, err2, "%s, %o", mkdir, tfs_dir, 0755);
            equality_of_existence =
              check_file_existence(rfs_dir) == check_file_existence(tfs_dir);
        };
        assert(c_expr{r1 == r2});
        assert(c_expr{err1 == err2});
        assert(c_expr{equality_of_existence});
    };
    :: d_step { 
        /* rmdir, check: retval, errno, existence */
        c_code {
            makecall(r1, err1, "%s", rmdir, rfs_dir);
            makecall(r2, err2, "%s", rmdir, tfs_dir);
            equality_of_existence =
              check_file_existence(rfs_dir) == check_file_existence(tfs_dir);
        };
        assert(c_expr{r1 == r2});
        assert(c_expr{err1 == err2});
        assert(c_expr{equality_of_existence});
    };
    :: d_step {
        /* open, check: errno, existence */
        c_code { 
            makecall(fd1, err1, "%s, %#x, %o", open, rfs_file, O_RDWR | O_CREAT, 0644);
            makecall(fd2, err2, "%s, %#x, %o", open, tfs_file, O_RDWR | O_CREAT, 0644);
            equality_of_existence =
              check_file_existence(rfs_dir) == check_file_existence(tfs_dir);
        };
        assert(c_expr{err1 == err2});
        assert(c_expr{equality_of_existence});
    };
    :: d_step {
        /* write, check: retval, errno, content */
        c_code {
            size_t writelen = pick_value(4096, 16384);
            char *data = malloc(writelen);
            makecall(r1, err1, "%d, %p, %zu", write, fd1, data, writelen);
            makecall(r2, err2, "%d, %p, %zu", write, fd2, data, writelen);
            free(data);
            /* Let's consider equality of content = true when neither rfs_file
               nor tfs_file exists. */
            if (!check_file_existence(rfs_file) && !check_file_existence(tfs_file))
                equality_of_content = true;
            else
                equality_of_content = compare_file_content(fd1, fd2) == 0;
        };
        assert(c_expr{r1 == r2});
        assert(c_expr{err1 == err2});
        assert(c_expr{equality_of_content});
    };
    :: d_step {
        /* close, check: retval, errno */
        c_code {
            makecall(r1, err1, "%d", close, fd1);
            makecall(r2, err2, "%d", close, fd2);
        };
        assert(c_expr{r1 == r2});
        assert(c_expr{err1 == err2});
    };
    :: d_step {
        /* unlink, check: retval, errno, existence */
        c_code {
            makecall(r1, err1, "%s", unlink, rfs_file);
            makecall(r2, err2, "%s", unlink, tfs_file);
            equality_of_existence =
              check_file_existence(rfs_dir) == check_file_existence(tfs_dir);
        };
        assert(c_expr{r1 == r2});
        assert(c_expr{err1 == err2});
        assert(c_expr{equality_of_existence});
    };
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        srand(time(0));
        /* Initialize path names */
        rfs_file = malloc(PATH_MAX * 4);
        rfs_dir = rfs_file + PATH_MAX;
        tfs_file = rfs_file + PATH_MAX * 2;
        tfs_dir = rfs_file + PATH_MAX * 3;
        snprintf(rfs_file, PATH_MAX, "%s/%s", rfs_path, filename);
        snprintf(rfs_dir, PATH_MAX, "%s/%s", rfs_path, dirname);
        snprintf(tfs_file, PATH_MAX, "%s/%s", tfs_path, filename);
        snprintf(tfs_dir, PATH_MAX, "%s/%s", tfs_path, dirname);
    };

    for (i : 1 .. nproc) {
        run worker();
    }

    /* Cleanup */
}

init
{
    run driver(1);
}
