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
    :: pick_num(num1);
       pick_num(num2);
       atomic {
        /* rename */
        c_code {
            makelog("BEGIN: rename\n");
            mountall();
            int dir_or_file = random() % 2;
            if( dir_or_file == 0 ){    
                int src_idx = Pworker->num1 % get_filepool_idx();
                int dst_idx = Pworker->num2 % get_filepool_idx();
                for (i = 0; i < get_n_fs(); ++i) {
                    char *rename_file_src;
                    char *rename_file_dst;
                    
                    size_t rename_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                    rename_file_src = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_src, rename_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                    rename_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                    rename_file_dst = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_dst, rename_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);

                    makecall(get_rets()[i], get_errs()[i], "%s,  %s", rename, rename_file_src, rename_file_dst);
                    free(rename_file_src);
                    free(rename_file_dst);
                }
            }
            else{
                int src_idx = Pworker->num1 % get_dirpool_idx();
                int dst_idx = Pworker->num2 % get_dirpool_idx();
                
                for (i = 0; i < get_n_fs(); ++i) {
                    char *rename_dir_src;
                    char *rename_dir_dst;
                    
                    size_t rename_dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
                    rename_dir_src = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_src, rename_dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[src_idx]);
               
                    rename_dirname_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_directorypool()[dst_idx]);
                    rename_dir_dst = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_dst, rename_dirname_len + 1, "%s%s", get_basepaths()[i], get_directorypool()[dst_idx]);

                    makecall(get_rets()[i], get_errs()[i], "%s,  %s", rename, rename_dir_src, rename_dir_dst);
                    free(rename_dir_src);
                    free(rename_dir_dst);
                }
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
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
                char *link_file_src;
                char *link_file_dst;
                    
                size_t link_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                link_file_src = calloc(1, link_filename_len+1);
                snprintf(link_file_src, link_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                link_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                link_file_dst = calloc(1, link_filename_len+1);
                snprintf(link_file_dst, link_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                makecall(get_rets()[i], get_errs()[i], "%s,  %s", link, link_file_src, link_file_dst);
                free(link_file_src);
                free(link_file_dst);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
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
                char *link_file_src;
                char *link_file_dst;
                    
                size_t link_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);
                link_file_src = calloc(1, link_filename_len+1);
                snprintf(link_file_src, link_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[src_idx]);

                link_filename_len = snprintf(NULL, 0, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                link_file_dst = calloc(1, link_filename_len+1);
                snprintf(link_file_dst, link_filename_len + 1, "%s%s", get_basepaths()[i], get_filepool()[dst_idx]);
                makecall(get_rets()[i], get_errs()[i], "%s,  %s", symlink, link_file_src, link_file_dst);
                free(link_file_src);
                free(link_file_dst);
            }
            expect(compare_equality_fexists(get_fslist(), get_n_fs(), get_testdirs()));
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
