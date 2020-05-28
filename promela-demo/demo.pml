#include "operations.h"

/* open() flags */
#define O_RDONLY    0
#define O_WRONLY    1
#define O_RDWR      2
#define O_CREAT     64  /* 0100 */
#define O_EXCL      128 /* 0200 */
#define O_TRUNC     512 /* 01000 */
#define O_APPEND    1024 /* 02000 */
#define O_SYNC      1052672 /* 04010000 */

int sequence;
int openflags;
bool openflags_used;

c_code {
\#include "fileutil.h"
\#include "bitree.h"

char *fslist[] = {"ext4", "ramfs", "xfs", "nfs"};
#define n_fs 4 
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

int openflags;
int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int i;

uint64_t state2;
uint64_t key;
bool duplicate;
int count;
};

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

inline dispatch_test() {
    if
        :: (openflags_used == 1) -> printf("select flag!\n"); select_open_flag(openflags);
        :: else -> skip;
    fi
    c_code {
        state2 = now.sequence;
        if (seq_contains(state2, OP_OPEN)) {
            /* If the sequence contains open(), use (openflags | sequence) as the search key */
            /* For this program there are 6 ops * 3 unit bits = 18 bits */
            key = (now.openflags << 18) | state2;
            openflags = now.openflags;
            now.openflags_used = 1;
        } else {
            key = state2;
        }
        duplicate = search(key);
        if (!duplicate) {
            printf("proc = [%d], count = %d, sequence = %06lo", Pworker->_pid, count, state2);
            if (seq_contains(state2, OP_OPEN)) {
                printf(", openflags = (%d) ", openflags);
                show_open_flags(openflags);
            }
            printf("\n");
        }
        while (!duplicate && state2 > 0) {
            switch (state2 & 0x7) {
            case OP_MKDIR:
                makelog("BEGIN: mkdir\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s, %o", mkdir, testdirs[i], 0755);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: mkdir\n");
                break;

            case OP_RMDIR:
                makelog("BEGIN: rmdir\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: rmdir\n");
                break;

            case OP_OPEN:
                makelog("BEGIN: open\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(fds[i], errs[i], "%s, %#x, %o", myopen, testfiles[i], openflags, 0644);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: open\n");
                break;
            
            case OP_WRITE:
                makelog("BEGIN: write\n");
                size_t writelen = pick_value(4096, 16384);
                char *data = malloc(writelen);
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%d, %p, %zu", write, fds[i], data, writelen);
                }

                free(data);
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                assert(compare_equality_fcontent(fslist, n_fs, testfiles, fds));
                makelog("END: write\n");
                break;

            case OP_CLOSE:
                makelog("BEGIN: close\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%d", close, fds[i]);
                }
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: close\n");
                break;

            case OP_UNLINK:
                makelog("BEGIN: unlink\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: unlink\n");
                break;
            }
            state2 >>= 3;
        }
        if (!duplicate) {
            insert_value(key);
            count++;
            cleanup();
        }
    }
}

inline enqueue_id(num) {
    sequence = sequence << 3;
    sequence = sequence | num;
    // open 18 bits (6 oct digits)
    sequence = sequence & 262143;
}

proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: atomic { 
        /* mkdir, check: retval, errno, existence */
        enqueue_id(OP_MKDIR);
        dispatch_test();
    };
    :: atomic { 
        /* rmdir, check: retval, errno, existence */
        enqueue_id(OP_RMDIR);
        dispatch_test();
    };
    :: atomic {
        /* open, check: errno, existence */
        enqueue_id(OP_OPEN);
        dispatch_test();
    };
    :: atomic {
        /* write, check: retval, errno, content */
        enqueue_id(OP_WRITE);
        dispatch_test();
    };
    :: atomic {
        /* close, check: retval, errno */
        enqueue_id(OP_CLOSE);
        dispatch_test();
    };
    :: atomic {
        /* unlink, check: retval, errno, existence */
        enqueue_id(OP_UNLINK);
        dispatch_test();
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
