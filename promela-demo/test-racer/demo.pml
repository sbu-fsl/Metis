c_code {
\#include "fileutil.h"
\#include "bitree.h"

char *fslist[] = {"ext4", "ramfs", "nfs", "xfs"};
#define n_fs 4 
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];
char *testfile_links[n_fs];
char *testfile_tmp[n_fs];
char* testmerged_files[n_fs];
char* testfiles_renamed[n_fs];

int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int i;

char* ret_value[n_fs];
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
            switch (state2 & 0xF) {
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
                makelog("BEGIN: file create\n");
                for (i = 0; i < n_fs; ++i) {
		    rets[i] = create(testfiles[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                makelog("END: file create\n");
                break;

            case 3:
                makelog("BEGIN: file list\n");
                for (i = 0; i < n_fs; ++i) {
		    ret_value[i][0] = '\0';
                    errs[i] = ls(ret_value[i], testdirs[i]);
                }
                assert(compare_filelist(ret_value, n_fs));
                makelog("END: file list\n");
                break;
            
            case 4:
                makelog("BEGIN: file remove\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%d", remove, fslist[i]);
                }

                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                makelog("END: file remove\n");
                break;

            case 5:
                makelog("BEGIN: file concatenate\n");
                for (i = 0; i < n_fs; i++) {
                    rets[i] = concat(testfiles[i], testfile_tmp[i], testmerged_files[i]);
                }
		// check content of the concat files
		assert(compare_equality_fcontent(fslist, n_fs, testmerged_files, fds));
                assert(compare_equality_values(fslist, n_fs, rets));
                makelog("END: file concatenate\n");
                break;

            case 6:
                makelog("BEGIN: file link\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", link, testfiles[i], testfile_links[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: file link\n");
                break;
            case 7:
                makelog("BEGIN: file rename\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", rename, testfiles[i], testfiles_renamed[i]);
                }
		assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
		swap(testfiles, testfiles_renamed, n_fs);
                makelog("END: file rename\n");
                break;
            case 8:
                makelog("BEGIN: file symlink\n");
                for (i = 0; i < n_fs; ++i) {
                    makecall(rets[i], errs[i], "%s", symlink, testfiles[i], testfile_links[i]);
                }
                assert(compare_equality_fexists(fslist, n_fs, testdirs));
                assert(compare_equality_values(fslist, n_fs, rets));
                assert(compare_equality_values(fslist, n_fs, errs));
                makelog("END: file symlink\n");
                break;
            }

            state2 >>= 4;
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
    sequence = sequence << 4;
    sequence = sequence | num;
    // open 32 bits (8 hex digits)
    sequence = sequence & 4294967295;
}
proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: d_step { /* mkdir*/
        enqueue_id(1);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /* file create*/
        enqueue_id(2);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file list*/
        enqueue_id(3);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file remove*/
	enqueue_id(4);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file concatenate*/
        enqueue_id(5);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file link*/
        enqueue_id(6);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file rename*/
        enqueue_id(7);
        printf("[%d] sequence = %x\n", _pid, sequence);
        dispatch_test();
    };
    :: d_step { /*file symlink*/
        enqueue_id(8);
        printf("[%d] sequence = %x\n", _pid, sequence);
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
	    // Test files
            len = snprintf(NULL, 0, "%s/test.txt", basepaths[i]);
            testfiles[i] = calloc(1, len + 1);
	    ret_value[i] = calloc(1, 1000);
            snprintf(testfiles[i], len + 1, "%s/test.txt", basepaths[i]);
	    // To test file rename.
            len = snprintf(NULL, 0, "%s/test_renamed.txt", basepaths[i]);
            testfiles_renamed[i] = calloc(1, len + 1);
	    snprintf(testfiles_renamed[i], len + 1, "%s/test.txt", basepaths[i]);
            //Test link files.
            len = snprintf(NULL, 0, "%s/test_link.txt", basepaths[i]);
            testfile_links[i] = calloc(1, len + 1);
            snprintf(testfile_links[i], len + 1, "%s/test_link.txt", basepaths[i]);
	    // Test tmp files for testing concat.
            len = snprintf(NULL, 0, "%s/test_tmp.txt", basepaths[i]);
            testfile_tmp[i] = calloc(1, len + 1);
            snprintf(testfile_tmp[i], len + 1, "%s/test_tmp.txt", basepaths[i]);
            // Test tmp files for testing concat.
            len = snprintf(NULL, 0, "%s/merged.txt", basepaths[i]);
            testmerged_files[i] = calloc(1, len + 1);
            snprintf(testmerged_files[i], len + 1, "%s/merged.txt", basepaths[i]);
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
