c_decl {
/* The escaped '#' is intended to prevent Spin from expanding the headers
 * when it's generating the C code */
\#include "fileutil.h"
\#include "config.h"
};
#include "parameters.pml"

/* DO NOT TOUCH THE COMMENT LINE BELOW */
/* The persistent content of the file systems */
c_track "get_fsimgs()[0]" "262144" "UnMatched";
c_track "get_fsimgs()[1]" "134217728" "UnMatched";

/* Abstract state signatures of the file systems */
/* DO NOT TOUCH THE COMMENT LINE ABOVE */
c_track "get_absfs()" "sizeof(get_absfs())";

proctype worker()
{
    /* Non-deterministic test loop */
    int create_flag, create_mode, write_flag, offset, writelen, writebyte, filelen, chmod_mode, chown_owner, chown_group;
    do 
    :: pick_create_open_flag(create_flag);
       pick_create_open_mode(create_mode);
       atomic {
        c_code {
            /* creat, check: return, errno, existence */
            makelog("BEGIN: create_file\n");
            mountall();
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d, 0%o", 
                        create_file, get_filepool()[i][src_idx], Pworker->create_flag, Pworker->create_mode);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d, 0%o", 
                        create_file, get_testfiles()[i], Pworker->create_flag, Pworker->create_mode);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: create_file\n");
        };
    };
    :: pick_write_open_flag(write_flag);
       pick_write_offset(offset);
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
            // Change Write Pattern Here
            generate_data(data, Pworker->writelen, Pworker->offset, BYTE_REPEAT, Pworker->writebyte);
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d, %p, %ld, %zu", 
                            write_file, get_filepool()[i][src_idx], Pworker->write_flag, data,
                            (off_t)Pworker->offset, (size_t)Pworker->writelen);
                }
                free(data);
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d, %p, %ld, %zu", 
                            write_file, get_testfiles()[i], Pworker->write_flag, data,
                            (off_t)Pworker->offset, (size_t)Pworker->writelen);
                }

                free(data);
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
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
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %ld", truncate, 
                        get_filepool()[i][src_idx], (off_t)Pworker->filelen);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %ld", truncate, 
                        get_testfiles()[i], (off_t)Pworker->filelen);
                }
            }
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
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s", unlink, 
                        get_filepool()[i][src_idx]);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s", unlink, 
                        get_testfiles()[i]);
                }
            }
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
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_dpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, 0%o", mkdir, 
                        get_directorypool()[i][src_idx], 0755);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, 0%o", mkdir, 
                        get_testdirs()[i], 0755);
                }
            }
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
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_dpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s", rmdir, 
                        get_directorypool()[i][src_idx]);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s", rmdir, 
                        get_testdirs()[i]);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: rmdir\n");
        }
    };
    :: pick_chmod_mode(chmod_mode);
       atomic {
        c_code {
            /* chmod, check: return, errno, absfs */
            makelog("BEGIN: chmod\n");
            mountall();
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, 0%o", 
                        chmod, get_filepool()[i][src_idx], Pworker->chmod_mode);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, 0%o", 
                        chmod, get_testfiles()[i], Pworker->chmod_mode);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: chmod\n");
        };
    };
    :: pick_chown_owner(chown_owner);
       atomic {
        c_code {
            /* chown_file, check: return, errno, absfs */
            makelog("BEGIN: chown_file\n");
            mountall();
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d", 
                        chown_file, get_filepool()[i][src_idx], (int) Pworker->chown_owner);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d", 
                        chown_file, get_testfiles()[i], (int) Pworker->chown_owner);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: chown_file\n");
        };
    };
    :: pick_chown_group(chown_group);
       atomic {
        c_code {
            /* chgrp_file, check: return, errno, absfs */
            makelog("BEGIN: chgrp_file\n");
            mountall();
            if (enable_fdpool) {
                int src_idx = pick_random(0, get_fpoolsize() - 1);
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d", 
                        chgrp_file, get_filepool()[i][src_idx], (int) Pworker->chown_group);
                }
            }
            else {
                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %d", 
                        chgrp_file, get_testfiles()[i], (int) Pworker->chown_group);
                }
            }
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
            expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
            expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));
            unmount_all_strict();
            makelog("END: chgrp_file\n");
        };
    };
    :: atomic {
        /* rename: run it only if the complex ops option enabled */
        c_expr {enable_complex_ops} ->
            c_code { 
                makelog("BEGIN: rename\n");
                mountall();
                int dir_or_file = random() % 2;
                /* Case of file */
                if (dir_or_file == 0) {
                    int src_idx = pick_random(0, get_fpoolsize() - 1);
                    int dst_idx = pick_random(0, get_fpoolsize() - 1);

                    for (i = 0; i < get_n_fs(); ++i) {
                        makecall(get_rets()[i], get_errs()[i], "%s, %s", rename, 
                            get_filepool()[i][src_idx], get_filepool()[i][dst_idx]);
                    }
                }
                /* Case of directory */
                else {
                    int src_idx = pick_random(0, get_dpoolsize() - 1);
                    int dst_idx = pick_random(0, get_dpoolsize() - 1);

                    for (i = 0; i < get_n_fs(); ++i) {
                        makecall(get_rets()[i], get_errs()[i], "%s, %s", rename, 
                            get_directorypool()[i][src_idx], get_directorypool()[i][dst_idx]);
                    }
                }
                expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
                expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
                expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));

                unmount_all_strict();
                makelog("END: rename\n");                
            }
    };

    :: atomic {
        /* link: run it only if the complex ops option enabled */
        c_expr {enable_complex_ops} ->
            c_code {
                makelog("BEGIN: link\n");
                mountall();

                int src_idx = pick_random(0, get_fpoolsize() - 1);
                int dst_idx = pick_random(0, get_fpoolsize() - 1);

                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %s", link, 
                       get_filepool()[i][src_idx], get_filepool()[i][dst_idx]);
                }
                expect(compare_equality_values(get_fslist(), get_n_fs(), get_rets()));
                expect(compare_equality_values(get_fslist(), get_n_fs(), get_errs()));
                expect(compare_equality_absfs(get_fslist(), get_n_fs(), get_absfs()));

                unmount_all_strict();
                makelog("END: link\n");
            }
    };
    :: atomic {
        /* symlink: run it only if the complex ops option enabled */
        c_expr {enable_complex_ops} ->
            c_code {
                makelog("BEGIN: symlink\n");
                mountall();

                int src_idx = pick_random(0, get_fpoolsize() - 1);
                int dst_idx = pick_random(0, get_fpoolsize() - 1);

                for (i = 0; i < get_n_fs(); ++i) {
                    makecall(get_rets()[i], get_errs()[i], "%s, %s", symlink, 
                        get_filepool()[i][src_idx], get_filepool()[i][dst_idx]);
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
        if (!enable_fdpool) {
            /*
             * Initialize test dirs and files names
             * Even though we do not need testfiles and testdirs with file
             * and dir pools, we cannot remove the definitions and 
             * declarations of these functions, otherwise SPIN pan.m complains
             */
            for (int i = 0; i < get_n_fs(); ++i) {
                size_t len = snprintf(NULL, 0, "%s/testdir", get_basepaths()[i]);
                get_testdirs()[i] = calloc(1, len + 1);
                snprintf(get_testdirs()[i], len + 1, "%s/testdir", get_basepaths()[i]);

                len = snprintf(NULL, 0, "%s/test.txt", get_basepaths()[i]);
                get_testfiles()[i] = calloc(1, len + 1);
                snprintf(get_testfiles()[i], len + 1, "%s/test.txt", get_basepaths()[i]);
            }
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
