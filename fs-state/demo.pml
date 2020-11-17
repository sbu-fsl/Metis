c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "config.h"
};

/* The persistent content of the file systems */
c_track "fsimg_ext4" "262144" "UnMatched";
c_track "fsimg_ext2" "262144" "UnMatched";
c_track "fsimg_jffs2" "262144" "UnMatched";
/* Abstract state signatures of the file systems */
c_track "absfs" "sizeof(absfs)";

proctype worker()
{
    /* Non-deterministic test loop */
    do 
    :: atomic {
       c_code {
           /* creat, check: errno, existence */
           makelog("BEGIN: create_file\n");
           mountall();
           for (i = 0; i < N_FS; ++i) {
               makecall(rets[i], errs[i], "%s, 0%o", create_file, testfiles[i], 0644);
               compute_abstract_state(basepaths[i], absfs[i]);
           }
           expect(compare_equality_fexists(fslist, N_FS, testdirs));
           expect(compare_equality_values(fslist, N_FS, errs));
           expect(compare_equality_absfs(fslist, N_FS, absfs));
           unmount_all();
           makelog("END: create_file\n");
       };
    };
    :: atomic {
        /* write, check: retval, errno, content */
        c_code {
            makelog("BEGIN: write_file\n");
            mountall();
            off_t offset = pick_value(0, 32768, 1024);
            size_t writelen = pick_value(0, 32768, 2048);
            char *data = malloc(writelen);
            generate_data(data, writelen, 0);
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s, %p, %ld, %zu", write_file, testfiles[i], data, offset, writelen);
                compute_abstract_state(basepaths[i], absfs[i]);
            }

            free(data);
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_fcontent(fslist, N_FS, testfiles));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
            makelog("END: write\n");
        };
    };
    :: atomic {
        /* truncate, check: retval, errno, existence */
        /* TODO: compare file length. Currently ftruncate is mainly
           intended to avoid long term ENOSPC of write() */
        c_code {
            makelog("BEGIN: truncate\n");
            mountall();
            off_t flen = pick_value(0, 200000, 10000);
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s, %ld", truncate, testfiles[i], flen);
                compute_abstract_state(basepaths[i], absfs[i]);
            }
            expect(compare_equality_fexists(fslist, N_FS, testfiles));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
            makelog("END: truncate\n");
        };
    };
    :: atomic {
        /* unlink, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: unlink\n");
            mountall();
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
                compute_abstract_state(basepaths[i], absfs[i]);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
            makelog("END: unlink\n");
        }
    };
    :: atomic {
        /* mkdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: mkdir\n");
            mountall();
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s, 0%o", mkdir, testdirs[i], 0755);
                compute_abstract_state(basepaths[i], absfs[i]);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
            makelog("END: mkdir\n");
        }
        // assert(! c_expr{ errs[0] == EEXIST && errs[1] == EEXIST && errs[2] == 0 });
    };
    :: atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            mountall();
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
                compute_abstract_state(basepaths[i], absfs[i]);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all();
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
        /* Initialize base paths */
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
