#include "operations.h"

c_decl {
\#include "fileutil.h"

char *fslist[] = {"ext4", "ext2", "xfs"};
#define n_fs    nelem(fslist)
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

void *fsimg_ext4, *fsimg_ext2, *fsimg_xfs;
int fsfd_ext4, fsfd_ext2, fsfd_xfs;
uint64_t absfs[n_fs];

int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int i;
};

int openflags;
/* The persistent content of the file systems */
c_track "fsimg_ext4" "262144" "UnMatched";
c_track "fsimg_ext2" "262144" "UnMatched";
c_track "fsimg_xfs" "16777216" "UnMatched";
/* Abstract state signatures of the file systems */
c_track "absfs" "sizeof(absfs)";

inline select_open_flag(flag) {
    /* O_RDONLY is 0 so there is no point writing an if-fi for it */
//     if
//         :: flag = flag | O_WRONLY;
//         :: skip;
//     fi
    flag = c_expr {O_RDWR | O_CREAT};
    if
        :: flag = flag & c_expr {~O_RDWR};
        :: skip;
    fi
    if
        :: flag = flag & c_expr {~O_CREAT};
        :: skip;
    fi
//     if
//         :: flag = flag | O_EXCL;
//         :: skip;
//     fi
//     if
//         :: flag = flag | O_TRUNC;
//         :: skip;
//     fi
//     if
//         :: flag = flag | O_APPEND;
//         :: skip;
//     fi
//     if
//         :: flag = flag | O_SYNC;
//         :: skip;
//     fi
}

proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: atomic {
        select_open_flag(openflags);
        c_code {
            /* open, check: errno, existence */
            makelog("BEGIN: open\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(fds[i], errs[i], "%s, %#x, %o", myopen, testfiles[i], now.openflags, 0644);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }
            expect(compare_equality_fexists(fslist, n_fs, testdirs));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: open\n");
        };
    };
    :: atomic {
        /* lseek */
        c_code {
            makelog("BEGIN: lseek\n");
            off_t offset = pick_value(0, 32768, 1024);
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d, %ld, %d", lseek, fds[i], offset, SEEK_SET);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }

            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: lseek\n");

        }
    };
    :: atomic {
        /* write, check: retval, errno, content */
        c_code {
            makelog("BEGIN: write\n");
            size_t writelen = pick_value(0, 32768, 2048);
            char *data = malloc(writelen);
            generate_data(data, writelen, 0);
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d, %p, %zu", write, fds[i], data, writelen);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }

            free(data);
            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_fcontent(fslist, n_fs, testfiles, fds));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: write\n");
        }
    };
    :: atomic {
        /* ftruncate, check: retval, errno, existence */
        /* TODO: compare file length. Currently ftruncate is mainly
           intended to avoid long term ENOSPC of write() */
        c_code {
            makelog("BEGIN: ftruncate\n");
            off_t flen = pick_value(0, 200000, 10000);
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d, %ld", ftruncate, fds[i], flen);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }
            expect(compare_equality_fexists(fslist, n_fs, testfiles));
            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: ftruncate\n");
        }
    };
    :: atomic {
        /* close all opened files */
        c_code {
            makelog("BEGIN: closeall\n");
            closeall();
            makelog("END: close\n");
        }
    };
    :: atomic {
        /* unlink, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: unlink\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }
            expect(compare_equality_fexists(fslist, n_fs, testdirs));
            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: unlink\n");
        }
    };
    :: atomic {
        /* mkdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: mkdir\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s, %o", mkdir, testdirs[i], 0755);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }
            expect(compare_equality_fexists(fslist, n_fs, testdirs));
            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
            makelog("END: mkdir\n");
        }
    };
    :: atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
                absfs[i] = compute_abstract_state(basepaths[i]);
            }
            expect(compare_equality_fexists(fslist, n_fs, testdirs));
            expect(compare_equality_values(fslist, n_fs, rets));
            expect(compare_equality_values(fslist, n_fs, errs));
            expect(compare_equality_absfs(fslist, n_fs, absfs));
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
        /* open and mmap the test f/s image as well as its heap memory */
        fsfd_ext4 = open("/tmp/fs-ext4.img", O_RDWR);
	    assert(fsfd_ext4 >= 0);
	    fsimg_ext4 = mmap(NULL, fsize(fsfd_ext4), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext4, 0);
        assert(fsimg_ext4 != MAP_FAILED);

        fsfd_ext2 = open("/tmp/fs-ext2.img", O_RDWR);
        assert(fsfd_ext2 >= 0);
        fsimg_ext2 = mmap(NULL, fsize(fsfd_ext2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext2, 0);
        assert(fsimg_ext2 != MAP_FAILED);

        fsfd_xfs = open("/dev/ram0", O_RDWR);
        assert(fsfd_xfs >= 0);
        fsimg_xfs = mmap(NULL, fsize(fsfd_xfs), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_xfs, 0);
        assert(fsimg_xfs != MAP_FAILED);

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
