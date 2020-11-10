#include "operations.h"

c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "config.h"
};

int openflags;
/* The persistent content of the file systems */
c_track "fsimg_ext2" "262144" "UnMatched";
c_track "fsimg_ext4" "262144" "UnMatched";
/* Abstract state signatures of the file systems */
c_track "absfs" "sizeof(absfs)";
c_track "&opened_files" "sizeof(opened_files)";

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
    :: if
        ::atomic {
            select_open_flag(openflags);
            c_code {
                /* open, check: errno, existence */
                makelog("BEGIN: open\n");
                mountall();
                /* log sequence: open:<path>:<flag>:<mode> */
                fprintf(seqfp, "open:%s:%d:%d\n", testfiles[0], now.openflags, 0644);
                for (i = 0; i < N_FS; ++i) {
		    errs[i] = my_open(i, testfiles[i], now.openflags, 0644);
                    //makecall(fds[i], errs[i], "%s, %#x, 0%o", my_open, i, testfiles[i], now.openflags, 0644);
                    compute_abstract_state(basepaths[i], absfs[i]);
                }
                expect(compare_equality_fexists(fslist, N_FS, testdirs));
                expect(compare_equality_values(fslist, N_FS, errs));
                expect(compare_equality_absfs(fslist, N_FS, absfs));
                unmount_all();
                makelog("END: open\n");
            };
            //assert(c_expr{filesystems_are_good()});
        };
        fi
    :: atomic {
        /* lseek */
        c_code {
            makelog("BEGIN: lseek\n");
            mountall();
            off_t offset = pick_value(0, 32768, 1024);
            /* log sequence: lseek:<offset>:<flag> */
            fprintf(seqfp, "lseek:%ld:%d\n", fds[i], offset, SEEK_SET);
            for (i = 0; i < N_FS; ++i) {
		rets[i] = my_lseek(i, testfiles[i], offset, SEEK_SET);
                //makecall(rets[i], errs[i], "%d, %ld, %d", my_lseek, i, fds[i], offset, SEEK_SET);
                compute_abstract_state(basepaths[i], absfs[i]);
            }

            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
            makelog("END: lseek\n");

        };
        assert(c_expr{filesystems_are_good()});
    };
   // :: atomic {
   //     /* write, check: retval, errno, content */
   //     c_code {
   //         makelog("BEGIN: write\n");
   //         mountall();
   //         size_t writelen = pick_value(0, 32768, 2048);
   //         char *data = malloc(writelen);
   //         generate_data(data, writelen, 0);
   //         /* log sequence: write:<writelen> */
   //         fprintf(seqfp, "write:%zu\n", writelen);
   //         for (i = 0; i < N_FS; ++i) {
   //             makecall(rets[i], errs[i], "%d, %p, %zu", write, fds[i], data, writelen);
   //             compute_abstract_state(basepaths[i], absfs[i]);
   //         }

   //         free(data);
   //         expect(compare_equality_values(fslist, N_FS, rets));
   //         expect(compare_equality_values(fslist, N_FS, errs));
   //         expect(compare_equality_fcontent(fslist, N_FS, testfiles, fds));
   //         expect(compare_equality_absfs(fslist, N_FS, absfs));
   //         unmount_all();
   //         makelog("END: write\n");
   //     };
   //     assert(c_expr{filesystems_are_good()});
   // };
   // :: atomic {
   //     /* ftruncate, check: retval, errno, existence */
   //     /* TODO: compare file length. Currently ftruncate is mainly
   //        intended to avoid long term ENOSPC of write() */
   //     c_code {
   //         makelog("BEGIN: ftruncate\n");
   //         mountall();
   //         off_t flen = pick_value(0, 200000, 10000);
   //         /* log sequence: ftruncate:<flen> */
   //         fprintf(seqfp, "ftruncate:%ld\n", flen);
   //         for (i = 0; i < N_FS; ++i) {
   //             makecall(rets[i], errs[i], "%d, %ld", ftruncate, fds[i], flen);
   //             compute_abstract_state(basepaths[i], absfs[i]);
   //         }
   //         expect(compare_equality_fexists(fslist, N_FS, testfiles));
   //         expect(compare_equality_values(fslist, N_FS, rets));
   //         expect(compare_equality_values(fslist, N_FS, errs));
   //         expect(compare_equality_absfs(fslist, N_FS, absfs));
   //         unmount_all();
   //         makelog("END: ftruncate\n");
   //     };
   //     assert(c_expr{filesystems_are_good()});
   // };
    :: atomic {
        /* close all opened files */
        c_code {
            makelog("BEGIN: closeall\n");
            mountall();
            /* log sequence: closeall */
            fprintf(seqfp, "closeall\n");
	    close_all_opened_files();
            unmount_all();
            makelog("END: close\n");
        }
        //assert(c_expr{filesystems_are_good()});
    };
   // :: atomic {
   //     /* unlink, check: retval, errno, existence */
   //     c_code {
   //         makelog("BEGIN: unlink\n");
   //         mountall();
   //         /* log sequence: unlink:<path> */
   //         fprintf(seqfp, "unlink:%s\n", testfiles[0]);
   //         for (i = 0; i < N_FS; ++i) {
   //             makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
   //             compute_abstract_state(basepaths[i], absfs[i]);
   //         }
   //         expect(compare_equality_fexists(fslist, N_FS, testdirs));
   //         expect(compare_equality_values(fslist, N_FS, rets));
   //         expect(compare_equality_values(fslist, N_FS, errs));
   //         expect(compare_equality_absfs(fslist, N_FS, absfs));
   //         unmount_all();
   //         makelog("END: unlink\n");
   //     }
   //     assert(c_expr{filesystems_are_good()});
   // };
   // :: atomic {
   //     /* mkdir, check: retval, errno, existence */
   //     c_code {
   //         makelog("BEGIN: mkdir\n");
   //         mountall();
   //         /* log sequence: mkdir:<path> */
   //         fprintf(seqfp, "mkdir:%s\n", testdirs[0]);
   //         for (i = 0; i < N_FS; ++i) {
   //             makecall(rets[i], errs[i], "%s, 0%o", mkdir, testdirs[i], 0755);
   //             compute_abstract_state(basepaths[i], absfs[i]);
   //         }
   //         expect(compare_equality_fexists(fslist, N_FS, testdirs));
   //         expect(compare_equality_values(fslist, N_FS, rets));
   //         expect(compare_equality_values(fslist, N_FS, errs));
   //         expect(compare_equality_absfs(fslist, N_FS, absfs));
   //         unmount_all();
   //         makelog("END: mkdir\n");
   //     }
   //     assert(c_expr{filesystems_are_good()});
   //     // assert(! c_expr{ errs[0] == EEXIST && errs[1] == EEXIST && errs[2] == 0 });
   // };
   // :: atomic {
   //     /* rmdir, check: retval, errno, existence */
   //     c_code {
   //         makelog("BEGIN: rmdir\n");
   //         mountall();
   //         fprintf(seqfp, "rmdir:%s\n", testdirs[0]);
   //         for (i = 0; i < N_FS; ++i) {
   //             makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
   //             compute_abstract_state(basepaths[i], absfs[i]);
   //         }
   //         expect(compare_equality_fexists(fslist, N_FS, testdirs));
   //         expect(compare_equality_values(fslist, N_FS, rets));
   //         expect(compare_equality_values(fslist, N_FS, errs));
   //         expect(compare_equality_absfs(fslist, N_FS, absfs));
   //         unmount_all();
   //         makelog("END: rmdir\n");
   //     }
   //     assert(c_expr{filesystems_are_good()});
   // };
    
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        /* Initialize base paths */
        init_opened_files_state();
        printf("%d file systems to test.\n", N_FS);
        for (int i = 0; i < N_FS; ++i) {
            size_t len = snprintf(NULL, 0, "/mnt/test-%s", fslist[i]);
            basepaths[i] = calloc(1, len + 1);
            snprintf(basepaths[i], len + 1, "/mnt/test-%s", fslist[i]);
        }
        /* Initialize test dirs and files names */
        for (int i = 0; i < N_FS; ++i) {
            size_t len = snprintf(NULL, 0, "%s/testdir", basepaths[i]);
            testdirs[i] = calloc(1, len + 1);
            snprintf(testdirs[i], len + 1, "%s/testdir", basepaths[i]);

            len = snprintf(NULL, 0, "%s/test.txt", basepaths[i]);
            testfiles[i] = calloc(1, len + 1);
            snprintf(testfiles[i], len + 1, "%s/test.txt", basepaths[i]);
        }
        /* open sequence file */
        seqfp = fopen("sequence.log", "w");
        assert(seqfp);

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
