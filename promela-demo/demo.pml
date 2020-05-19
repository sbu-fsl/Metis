c_code {
\#include "fileutil.h"
\#include "bitree.h"

char *fslist[] = {"ext4", "ramfs", "xfs", "nfs"};
#define n_fs 4 
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int i;

uint64_t state2;
bool duplicate;
int count;
};

int sequence;

inline dispatch_test() {
    c_code {
        state2 = now.sequence;
        duplicate = search(state2);
        while (!duplicate && state2 > 0) {
            switch (state2 & 0x7) {
            case 1:
                makelog("BEGIN: mkdir\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s, %o", mkdir, testdirs[i], 0755);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: mkdir\n");
                break;

            case 2:
                makelog("BEGIN: rmdir\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: rmdir\n");
                break;

            case 3:
                makelog("BEGIN: open\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(fds[i], errs[i], "%s, %#x, %o", open, testfiles[i], O_RDWR | O_CREAT, 0644);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: open\n");
                break;
            
            case 4:
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

            case 5:
                makelog("BEGIN: close\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%d", close, fds[i]);
                }
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: close\n");
                break;

            case 6:
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
            insert_value(now.sequence);
            count++;
            printf("Sequence count: %d\n", count);
            /* cleanup : close all fds */
            for (i = 0; i < n_fs; ++i) {
                close(fds[i]);
            }
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
    :: d_step { 
        /* mkdir, check: retval, errno, existence */
        enqueue_id(1);
        printf("[%d] sequence = %o\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { 
        /* rmdir, check: retval, errno, existence */
        enqueue_id(2);
        printf("[%d] sequence = %o\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step {
        /* open, check: errno, existence */
        enqueue_id(3);
        printf("[%d] sequence = %o\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step {
        /* write, check: retval, errno, content */
        enqueue_id(4);
        printf("[%d] sequence = %o\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step {
        /* close, check: retval, errno */
        enqueue_id(5);
        printf("[%d] sequence = %o\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step {
        /* unlink, check: retval, errno, existence */
        enqueue_id(6);
        printf("[%d] sequence = %o\n", _pid, sequence);
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
