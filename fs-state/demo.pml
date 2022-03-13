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
    int offset, writelen, writebyte, filelen, num1, num2;
    do 
    :: atomic {
       c_code {
           /* creat, check: errno, existence */
           makelog("BEGIN: create_file\n");
           mountall();
           for (i = 0; i < N_FS; ++i) {
               makecall(rets[i], errs[i], "%s, 0%o", create_file, testfiles[i], 0644);
           }
           expect(compare_equality_fexists(fslist, N_FS, testdirs));
           expect(compare_equality_values(fslist, N_FS, errs));
           expect(compare_equality_absfs(fslist, N_FS, absfs));
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
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s, %p, %ld, %zu", write_file, testfiles[i], data,
                         (off_t)Pworker->offset, (size_t)Pworker->writelen);
            }

            free(data);
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_fcontent(fslist, N_FS, testfiles));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
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
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s, %ld", truncate, testfiles[i], (off_t)Pworker->filelen);
            }
            expect(compare_equality_fexists(fslist, N_FS, testfiles));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all_strict();
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
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
            unmount_all_strict();
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
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
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
            for (i = 0; i < N_FS; ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));
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
//                int num1 = random() % filepool_idx;
//		int num2 = random() % filepool_idx;

                for (i = 0; i < N_FS; ++i) {
                    char *rename_file_src;
		    char *rename_file_dst;
                    
                    size_t rename_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[Pworker->num1]);
                    rename_file_src = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_src, rename_filename_len + 1, "%s%s", basepaths[i], filepool[Pworker->num1]);

		    rename_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[Pworker->num2]);
                    rename_file_dst = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_dst, rename_filename_len + 1, "%s%s", basepaths[i], filepool[Pworker->num2]);

                
                    makecall(rets[i], errs[i], "%s,  %s", mv, rename_file_src, rename_file_dst);
                }
            }
            else{
//                int num1 = random() % dirpool_idx;
//		int num2 = random() % dirpool_idx;

                for (i = 0; i < N_FS; ++i) {
                    char *rename_dir_src;
		    char *rename_dir_dst;
                    
                    size_t rename_dirname_len = snprintf(NULL, 0, "%s%s", basepaths[i], directorypool[Pworker->num1]);
                    rename_dir_src = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_src, rename_dirname_len + 1, "%s%s", basepaths[i], directorypool[Pworker->num1]);
               
 		    rename_dirname_len = snprintf(NULL, 0, "%s%s", basepaths[i], directorypool[Pworker->num2]);
                    rename_dir_dst = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_dst, rename_dirname_len + 1, "%s%s", basepaths[i], directorypool[Pworker->num2]);

                    makecall(rets[i], errs[i], "%s,  %s", mv, rename_dir_src, rename_dir_dst);
                }

            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));

            unmount_all_strict();
            makelog("END: rename\n");
        }
    };
 
    od
};

proctype driver(int nproc)
{
    int i;
    c_code {
        filecount = 3;
        directorycount = 3;
	pool_depth = 3;
	void dfs(int directorycount, int filecount, int pool_depth, char** current, int size){
        	int newnames_len = 0;
	        char *newpool[100];
         	for(int i = 0; i < size; i++){
                        for(int j = 0; j < directorycount; j++){
                                char *newname;
                                size_t len = snprintf(NULL, 0, "%s/d-%d", current[i], j);
                                newpool[newnames_len] = calloc(1, 1+len);
                                snprintf(newpool[newnames_len], 1+len, "%s/d-%d", current[i], j);

                                directorypool[dirpool_idx] = calloc(1, 1+len);
                                snprintf(directorypool[dirpool_idx], 1+len, "%s/d-%d", current[i], j);
                                dirpool_idx++;
                                newnames_len++;
                        }
                }
                for(int i = 0; i < size; i++){
                        for(int j = 0; j < filecount; j++){
                                char *newname;
                                size_t len = snprintf(NULL, 0, "%s/f-%d.txt", current[i], j);

                                filepool[filepool_idx] = calloc(1, 1+len);
                                snprintf(filepool[filepool_idx], 1+len, "%s/f-%d.txt", current[i], j);
                                filepool_idx++;
                        }
                }
	        if(pool_depth == 1){
        	        return;
	        }

        	dfs(directorycount, filecount, pool_depth-1, newpool, newnames_len);
	}

        start_perf_metrics_thread();
        /* Initialize test dirs and files names */

	char *current[100];

	size_t len = snprintf(NULL, 0, "%s");
        current[0] = calloc(1, len + 1);
        snprintf(current[0], len + 1, "");


        len = snprintf(NULL, 0, "/test.txt");
        filepool[filepool_idx] = calloc(1, 1+len);
        snprintf(filepool[filepool_idx], 1+len, "/test.txt");
        filepool_idx++;


        len = snprintf(NULL, 0, "/testdir");
        directorypool[dirpool_idx] = calloc(1, 1+len);
        snprintf(directorypool[dirpool_idx], 1+len, "/testdir");
        dirpool_idx++;

 
	dfs(directorycount, filecount, pool_depth, current, 1);
	
	makelog("Filepool contents: ");
        for(int i = 0; i < filepool_idx; i++){
                makelog("%s\n", filepool[i]);
        }

        makelog("Directory pool contents: ");

        for(int i = 0; i < dirpool_idx; i++){
                makelog("%s\n", directorypool[i]);
        }	
	
        for (int i = 0; i < N_FS; ++i) {
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
}

init
{
    run driver(1);
}
