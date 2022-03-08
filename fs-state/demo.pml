c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "whichconfig.h"
};
#include "parameters.pml"

/* The persistent content of the file systems */
c_track "fsimgs[0]" "262144" "UnMatched";
c_track "fsimgs[1]" "262144" "UnMatched";
/* Abstract state signatures of the file systems */
c_track "absfs" "sizeof(absfs)";

proctype worker()
{
    /* Non-deterministic test loop */
    int offset, writelen, writebyte, filelen;
    do 
    :: atomic {
       c_code {
           /* creat, check: errno, existence */
           makelog("BEGIN: create_file\n");
           mountall();
           for (i = 0; i < get_n_fs(); ++i) {
               makecall(rets[i], errs[i], "%s, 0%o", create_file, testfiles[i], 0644);
           }
           expect(compare_equality_fexists(get_fslist(), get_n_fs(), testdirs));
           expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
           expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
           unmount_all_strict();
           makelog("END: create_file\n");
       };
    };
    :: pick_write_offset(offset);
       pick_write_size(writelen);
       pick_write_byte(writebyte);
       atomic {
        /* write, check: retval, errno, content */
        c_code {
            makelog("BEGIN: write_file\n");
            mountall();
            // off_t offset = pick_value(0, 32768, 1024);
            // size_t writelen = pick_value(0, 32768, 2048);
            char *data = malloc(Pworker->writelen);
            generate_data(data, Pworker->writelen, Pworker->writebyte);
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(rets[i], errs[i], "%s, %p, %ld, %zu", write_file, testfiles[i], data,
                         (off_t)Pworker->offset, (size_t)Pworker->writelen);
            }

            free(data);
            expect(compare_equality_values(get_fslist(), get_n_fs(), rets));
            expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), testfiles));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
            unmount_all_strict();
            makelog("END: write_file\n");
        };
    };
    :: pick_truncate_len(filelen);
       atomic {
        /* truncate, check: retval, errno, existence */
        /* TODO: compare file length. Currently ftruncate is mainly
           intended to avoid long term ENOSPC of write() */
        c_code {
            makelog("BEGIN: truncate\n");
            mountall();
            // off_t flen = pick_value(0, 200000, 10000);
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(rets[i], errs[i], "%s, %ld", truncate, testfiles[i], (off_t)Pworker->filelen);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), testfiles));
            expect(compare_equality_values(get_fslist(), get_n_fs(), rets));
            expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
            unmount_all_strict();
            makelog("END: truncate\n");
        };
    };
    :: atomic {
        /* unlink, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: unlink\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), testdirs));
            expect(compare_equality_values(get_fslist(), get_n_fs(), rets));
            expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
            unmount_all_strict();
            makelog("END: unlink\n");
        }
    };
    :: atomic {
        /* mkdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: mkdir\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(rets[i], errs[i], "%s, 0%o", mkdir, testdirs[i], 0755);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), testdirs));
            expect(compare_equality_values(get_fslist(), get_n_fs(), rets));
            expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
            unmount_all_strict();
            makelog("END: mkdir\n");
        }
        // assert(! c_expr{ errs[0] == EEXIST && errs[1] == EEXIST && errs[2] == 0 });
    };
    :: atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), testdirs));
            expect(compare_equality_values(get_fslist(), get_n_fs(), rets));
            expect(compare_equality_values(get_fslist(), get_n_fs(), errs));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), absfs));
            unmount_all_strict();
            makelog("END: rmdir\n");
        }
    };
    
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        start_perf_metrics_thread();
        /* Initialize test dirs and files names */
        for (int i = 0; i < get_n_fs(); ++i) {
            size_t len = snprintf(NULL, 0, "%s/testdir", get_basepaths()[i]);
            testdirs[i] = calloc(1, len + 1);
            snprintf(testdirs[i], len + 1, "%s/testdir", get_basepaths()[i]);

            len = snprintf(NULL, 0, "%s/test.txt", get_basepaths()[i]);
            testfiles[i] = calloc(1, len + 1);
            snprintf(testfiles[i], len + 1, "%s/test.txt", get_basepaths()[i]);
        }
    };

    for (i : 1 .. nproc) {
        run worker();
    }
}

init
{
    run driver(1);
}
