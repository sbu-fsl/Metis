c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "config.h"
};
#include "parameters.pml"

/* DO NOT TOUCH THE COMMENT LINE BELOW */
/* The persistent content of the file systems */

/* Abstract state signatures of the file systems */
/* DO NOT TOUCH THE COMMENT LINE ABOVE */
c_track "get_absfs()" "sizeof(get_absfs())";

proctype worker()
{
    /* Non-deterministic test loop */
    int offset, writelen, writebyte, filelen, num1, num2;
    do 
    :: pick_num(num1);
        atomic {
        c_code {
            /* creat, check: errno, existence */
            makelog("BEGIN: create_file\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                char *file_src;
                int src_idx = Pworker->num1 % get_filepool_idx();
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                get_testfiles()[i] = file_src;
                makecall(get_rets()[i], get_errs()[i], "%s, 0%o", create_file, file_src, 0644);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testfiles()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: create_file\n");
        };
    };
    :: pick_write_offset(offset);
       pick_write_size(writelen);
       pick_write_byte(writebyte);
       pick_num(num1);
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
                char *file_src;
                int src_idx = Pworker->num1 % get_filepool_idx();
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                get_testfiles()[i] = file_src;
                makecall(get_rets()[i], get_errs()[i], "%s, %p, %ld, %zu", write_file, file_src, data,
                         (off_t)Pworker->offset, (size_t)Pworker->writelen);
            }
            free(data);
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: write_file\n");
        };
    };
    :: pick_truncate_len(filelen);
       pick_num(num1);
       atomic {
        /* truncate, check: retval, errno, existence */
        /* TODO: compare file length. Currently ftruncate is mainly
           intended to avoid long term ENOSPC of write() */
        c_code {
            makelog("BEGIN: truncate\n");
            mountall();
            // off_t flen = pick_value(0, 200000, 10000);
            for (i = 0; i < get_n_fs(); ++i) {
                char *file_src;
                int src_idx = Pworker->num1 % get_filepool_idx();
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                get_testfiles()[i] = file_src;
                makecall(get_rets()[i], get_errs()[i], "%s, %ld", truncate, file_src, (off_t)Pworker->filelen);
            }
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: truncate\n");
        };
    };
    :: pick_num(num1);
       atomic {
        /* unlink, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: unlink\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                char *file_src;
                int src_idx = Pworker->num1 % get_filepool_idx();
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                get_testfiles()[i] = file_src;
                makecall(get_rets()[i], get_errs()[i], "%s", unlink, file_src);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testfiles()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: unlink\n");
        }
    };
    :: pick_num(num1);
       atomic {
        /* mkdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: mkdir\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                char *dir_src;
                int src_idx = Pworker->num1 % get_dirpool_idx();
                size_t dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
                dir_src = calloc(1, dirname_len+1);
                snprintf(dir_src, dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);

                get_testdirs()[i] = dir_src;
                makecall(get_rets()[i], get_errs()[i], "%s, 0%o", mkdir, dir_src, 0755);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testdirs()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: mkdir\n");
        }
        // assert(! c_expr{ get_errs()[0] == EEXIST && get_errs()[1] == EEXIST && get_errs()[2] == 0 });
    };
    ::  pick_num(num1);
        atomic {
        /* rmdir, check: retval, errno, existence */
        c_code {
            makelog("BEGIN: rmdir\n");
            mountall();
            for (i = 0; i < get_n_fs(); ++i) {
                char *dir_src;
                int src_idx = Pworker->num1 % get_dirpool_idx();
                size_t dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
                dir_src = calloc(1, dirname_len+1);
                snprintf(dir_src, dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);

                get_testdirs()[i] = dir_src;
                makecall(get_rets()[i], get_errs()[i], "%s", rmdir, get_testdirs()[i]);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testdirs()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: rmdir\n");
        }
    };
    :: pick_num(num1);
       pick_num(num2);
       atomic {
        /* rename */
        c_code {
            makelog("BEGIN: rename\n");
            mountall();
            int dir_or_file = random() % 2;
            /* Case of file */
            if (dir_or_file == 0) {    
                int src_idx = Pworker->num1 % get_filepool_idx();
                int dst_idx = Pworker->num2 % get_filepool_idx();
                for (i = 0; i < get_n_fs(); ++i) {
                    char *file_src;
                    char *file_dst;
                    
                    size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                    file_src = calloc(1, filename_len + 1);
                    snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                    filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                    file_dst = calloc(1, filename_len + 1);
                    snprintf(file_dst, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);

                    get_testfiles()[i] = file_src;
                    get_testfiles_dst()[i] = file_dst;

                    makecall(get_rets()[i], get_errs()[i], "%s,  %s", rename, file_src, file_dst);
                }
                expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
                expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles_dst()));
                for (i = 0; i < get_n_fs(); ++i) {
                    free(get_testfiles()[i]);
                    free(get_testfiles_dst()[i]);
                }
            }
            /* Case of directory */
            else {
                int src_idx = Pworker->num1 % get_dirpool_idx();
                int dst_idx = Pworker->num2 % get_dirpool_idx();
                
                for (i = 0; i < get_n_fs(); ++i) {
                    char *dir_src;
                    char *dir_dst;
                    
                    size_t dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
                    dir_src = calloc(1, dirname_len+1);
                    snprintf(dir_src, dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
               
                    dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[dst_idx]);
                    dir_dst = calloc(1, dirname_len+1);
                    snprintf(dir_dst, dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[dst_idx]);

                    get_testdirs()[i] = dir_src;
                    get_testdirs_dst()[i] = dir_dst;

                    makecall(get_rets()[i], get_errs()[i], "%s,  %s", rename, dir_src, dir_dst);
                }
                expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
                expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs_dst()));
                for (i = 0; i < get_n_fs(); ++i) {
                    free(get_testdirs()[i]);
                    free(get_testdirs_dst()[i]);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));

            unmount_all_strict();
            makelog("END: rename\n");
        }
    };

    :: pick_num(num1);
       pick_num(num2);
       atomic {
        /* link */
        c_code {
            makelog("BEGIN: link\n");
            mountall();

            int src_idx = Pworker->num1 % get_filepool_idx();
            int dst_idx = Pworker->num2 % get_filepool_idx();

            for (i = 0; i < get_n_fs(); ++i) {
                char *file_src;
                char *file_dst;
                    
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                file_dst = calloc(1, filename_len+1);
                snprintf(file_dst, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);

                get_testfiles()[i] = file_src;
                get_testfiles_dst()[i] = file_dst;                

                makecall(get_rets()[i], get_errs()[i], "%s,  %s", link, file_src, file_dst);
            }
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles_dst()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
                free(get_testfiles_dst()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));

            unmount_all_strict();
            makelog("END: link\n");
        }
    };
    :: pick_num(num1);
       pick_num(num2);
       atomic {
        /* symlink */
        c_code {
            makelog("BEGIN: symlink\n");
            mountall();

            int src_idx = Pworker->num1 % get_filepool_idx();
            int dst_idx = Pworker->num2 % get_filepool_idx();

            for (i = 0; i < get_n_fs(); ++i) {
                char *file_src;
                char *file_dst;
                    
                size_t filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                file_src = calloc(1, filename_len+1);
                snprintf(file_src, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                file_dst = calloc(1, filename_len+1);
                snprintf(file_dst, filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);

                get_testfiles()[i] = file_src;
                get_testfiles_dst()[i] = file_dst;

                makecall(get_rets()[i], get_errs()[i], "%s,  %s", symlink, file_src, file_dst);
            }
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles()));
            expect(compare_equality_fcontent(get_fslist(), get_n_fs(), get_testfiles_dst()));
            for (i = 0; i < get_n_fs(); ++i) {
                free(get_testfiles()[i]);
                free(get_testfiles_dst()[i]);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));

            unmount_all_strict();
            makelog("END: symlink\n");
        }
    };
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        start_perf_metrics_thread();
    };

    for (i : 1 .. nproc) {
        run worker();
    }

}

init
{
    run driver(1);
}
