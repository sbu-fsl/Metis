#include "operations.h"

c_code {
\#include "fileutil.h"

char *fslist[] = {"ext4"};
#define n_fs 1 
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

int openflags;
int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int i;
};

c_track "fsimg" "262144";
c_track "&errno" "sizeof(int)";

inline select_open_flag(flag) {
    openflags_used = 0;
    /* O_RDONLY is 0 so there is no point writing an if-fi for it */
    if
        :: flag = flag | O_WRONLY;
        :: skip;
    fi
    if
        :: flag = flag | O_RDWR;
        :: skip;
    fi
    if
        :: flag = flag | O_CREAT;
        :: skip;
    fi
    if
        :: flag = flag | O_EXCL;
        :: skip;
    fi
    if
        :: flag = flag | O_TRUNC;
        :: skip;
    fi
    if
        :: flag = flag | O_APPEND;
        :: skip;
    fi
    if
        :: flag = flag | O_SYNC;
        :: skip;
    fi
}

proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: atomic {
        c_code {
            /* open, check: errno, existence */
            makelog("BEGIN: open\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(fds[i], errs[i], "%s, %#x, %o", myopen, testfiles[i], O_RDWR | O_CREAT, 0644);
            }
            assert(compare_equality_fexists(fslist, n_fs, testdirs));
            assert(compare_equality_values(fslist, n_fs, errs));
            makelog("END: open\n");
        }
    };
    :: atomic {
        /* write, check: retval, errno, content */
        c_code {
            makelog("BEGIN: write\n");
            size_t writelen = pick_value(1, 200000);
            char *data = malloc(writelen);
	        generate_data(data, writelen, 255);
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d, %p, %zu", write, fds[i], data, writelen);
            }

            free(data);
            assert(compare_equality_values(fslist, n_fs, rets));
            assert(compare_equality_values(fslist, n_fs, errs));
            assert(compare_equality_fcontent(fslist, n_fs, testfiles, fds));
            makelog("END: write\n");
        }
    };
    :: atomic {
        /* close, check: retval, errno */
        c_code {
            makelog("BEGIN: close\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d", close, fds[i]);
            }
            assert(compare_equality_values(fslist, n_fs, rets));
            assert(compare_equality_values(fslist, n_fs, errs));
            makelog("END: close\n");
        }
    };
    :: atomic {
        /* unlink, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: unlink\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
            }
            assert(compare_equality_fexists(fslist, n_fs, testdirs));
            assert(compare_equality_values(fslist, n_fs, rets));
            assert(compare_equality_values(fslist, n_fs, errs));
            makelog("END: unlink\n");
        }
    };
    :: atomic {
        /* mkdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: mkdir\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s, %o", mkdir, testdirs[i], 0755);
            }
            assert(compare_equality_fexists(fslist, n_fs, testdirs));
            assert(compare_equality_values(fslist, n_fs, rets));
            assert(compare_equality_values(fslist, n_fs, errs));
            makelog("END: mkdir\n");
        }
    };
    :: atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
            }
            assert(compare_equality_fexists(fslist, n_fs, testdirs));
            assert(compare_equality_values(fslist, n_fs, rets));
            assert(compare_equality_values(fslist, n_fs, errs));
            makelog("END: rmdir\n");
        }
    };
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        srand(time(0));
        current_utc_time(&begin_time);
        /* Initialize base paths */
        printf("%d file systems to test.\n", n_fs);
        for (int i = 0; i < n_fs; ++i) {
            size_t len = snprintf(NULL, 0, "/mnt/test-%s", fslist[i]);
            basepaths[i] = calloc(1, len + 1);
            snprintf(basepaths[i], len + 1, "/mnt/test-%s", fslist[i]);
        }
        /* Initialize test dirs and files names */
        for (int i = 0; i < n_fs; ++i) {
            size_t len = snprintf(NULL, 0, "%s/testdir", basepaths[i]);
            testdirs[i] = calloc(1, len + 1);
            snprintf(testdirs[i], len + 1, "%s/testdir", basepaths[i]);

            len = snprintf(NULL, 0, "%s/test.txt", basepaths[i]);
            testfiles[i] = calloc(1, len + 1);
            snprintf(testfiles[i], len + 1, "%s/test.txt", basepaths[i]);
        }
        /* open and mmap the test f/s image */
        fsfd = open("/tmp/fs0.img", O_RDWR);
        fsimg = mmap(NULL, fsize(fsfd), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd, 0);
        assert(fsimg != MAP_FAILED);
        atexit(cleanup);
    };

    for (i : 1 .. nproc) {
        run worker();
    }
}

init
{
    run driver(1);
}
