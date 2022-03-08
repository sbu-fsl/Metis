c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "whichconfig.h"
};
#include "parameters.pml"

/* The persistent content of the file systems */
c_track "get_fsimgs()[0]" "262144" "UnMatched";
c_track "get_fsimgs()[1]" "262144" "UnMatched";
/* Abstract state signatures of the file systems */
c_track "get_absfs()" "sizeof(get_absfs())";

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
               makecall(get_rets()[i], get_errs()[i], "%s, 0%o", create_file, get_testfiles()[i], 0644);
           }
           expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
           expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
           expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
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
                makecall(get_rets()[i], get_errs()[i], "%s, %p, %ld, %zu", write_file, get_testfiles()[i], data,
                         (off_t)Pworker->offset, (size_t)Pworker->writelen);
            }

            free(data);
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
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
                makecall(get_rets()[i], get_errs()[i], "%s, %ld", truncate, get_testfiles()[i], (off_t)Pworker->filelen);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testfiles()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
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
                makecall(get_rets()[i], get_errs()[i], "%s", unlink, get_testfiles()[i]);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
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
                makecall(get_rets()[i], get_errs()[i], "%s, 0%o", mkdir, get_testdirs()[i], 0755);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: mkdir\n");
        }
        // assert(! c_expr{ get_errs()[0] == EEXIST && get_errs()[1] == EEXIST && get_errs()[2] == 0 });
    };
    :: atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                makecall(get_rets()[i], get_errs()[i], "%s", rmdir, get_testdirs()[i]);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
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
            get_testdirs()[i] = calloc(1, len + 1);
            snprintf(get_testdirs()[i], len + 1, "%s/testdir", get_basepaths()[i]);

            len = snprintf(NULL, 0, "%s/test.txt", get_basepaths()[i]);
            get_testfiles()[i] = calloc(1, len + 1);
            snprintf(get_testfiles()[i], len + 1, "%s/test.txt", get_basepaths()[i]);
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
