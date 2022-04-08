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
		
		int src_idx = Pworker->num1 % filepool_idx;
		int dst_idx = Pworker->num2 % filepool_idx;
                for (i = 0; i < N_FS; ++i) {
                    char *rename_file_src;
		    char *rename_file_dst;
                    
                    size_t rename_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[src_idx]);
                    rename_file_src = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_src, rename_filename_len + 1, "%s%s", basepaths[i], filepool[src_idx]);

		    rename_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[dst_idx]);
                    rename_file_dst = calloc(1, rename_filename_len+1);
                    snprintf(rename_file_dst, rename_filename_len + 1, "%s%s", basepaths[i], filepool[dst_idx]);

                
                    makecall(rets[i], errs[i], "%s,  %s", rename, rename_file_src, rename_file_dst);
                    free(rename_file_src);
                    free(rename_file_dst);
                }
            }
            else{
		int src_idx = Pworker->num1 % dirpool_idx;
		int dst_idx = Pworker->num2 % dirpool_idx;
                
                for (i = 0; i < N_FS; ++i) {
                    char *rename_dir_src;
		    char *rename_dir_dst;
                    
                    size_t rename_dirname_len = snprintf(NULL, 0, "%s%s", basepaths[i], directorypool[src_idx]);
                    rename_dir_src = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_src, rename_dirname_len + 1, "%s%s", basepaths[i], directorypool[src_idx]);
               
 		    rename_dirname_len = snprintf(NULL, 0, "%s%s", basepaths[i], directorypool[dst_idx]);
                    rename_dir_dst = calloc(1, rename_dirname_len+1);
                    snprintf(rename_dir_dst, rename_dirname_len + 1, "%s%s", basepaths[i], directorypool[dst_idx]);

                    makecall(rets[i], errs[i], "%s,  %s", rename, rename_dir_src, rename_dir_dst);
                    free(rename_dir_src);
                    free(rename_dir_dst);
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

    :: pick_num(num1);
       pick_num(num2);
       atomic {
        /* link */
        c_code {
            makelog("BEGIN: link\n");
            mountall();

            int src_idx = Pworker->num1 % filepool_idx;
            int dst_idx = Pworker->num2 % filepool_idx;

		
            for (i = 0; i < N_FS; ++i) {
                char *link_file_src;
	 	char *link_file_dst;
                    
                size_t link_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[src_idx]);
                link_file_src = calloc(1, link_filename_len+1);
                snprintf(link_file_src, link_filename_len + 1, "%s%s", basepaths[i], filepool[src_idx]);

		link_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[dst_idx]);
                link_file_dst = calloc(1, link_filename_len+1);
                snprintf(link_file_dst, link_filename_len + 1, "%s%s", basepaths[i], filepool[dst_idx]);
                makecall(rets[i], errs[i], "%s,  %s", link, link_file_src, link_file_dst);
                free(link_file_src);
                free(link_file_dst);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));

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

            int src_idx = Pworker->num1 % filepool_idx;
	    int dst_idx = Pworker->num2 % filepool_idx;

            for (i = 0; i < N_FS; ++i) {
                char *link_file_src;
	 	char *link_file_dst;
                    
                size_t link_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[src_idx]);
                link_file_src = calloc(1, link_filename_len+1);
                snprintf(link_file_src, link_filename_len + 1, "%s%s", basepaths[i], filepool[src_idx]);

		link_filename_len = snprintf(NULL, 0, "%s%s", basepaths[i], filepool[dst_idx]);
                link_file_dst = calloc(1, link_filename_len+1);
                snprintf(link_file_dst, link_filename_len + 1, "%s%s", basepaths[i], filepool[dst_idx]);
                makecall(rets[i], errs[i], "%s,  %s", symlink, link_file_src, link_file_dst);
                free(link_file_src);
                free(link_file_dst);
            }
            expect(compare_equality_fexists(fslist, N_FS, testdirs));
            expect(compare_equality_values(fslist, N_FS, rets));
            expect(compare_equality_values(fslist, N_FS, errs));
            expect(compare_equality_absfs(fslist, N_FS, absfs));

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
        filecount = 3;
        directorycount = 3;
	pool_depth = 3;
	max_name_len = 10;
	//current is the list of directories previous depth
	//size is current's size.
	void dfs(int directorycount, int filecount, int pool_depth, int max_name_len, char** current, int size){
        	int newnames_len = 0;
		//newpool -> directories at the current depth.
	        char *newpool[100];
		int append = 0;
		//iterate through directories in the previous depth(stored in current), append each d-[j] to each current[i] and add to directorypool
		//also add this to the newpool
         	for(int i = 0; i < size; i++){
                        for(int j = 0; j < directorycount; j++){
                                char *newname;
				append = max_name_len - 2;
                                size_t len = snprintf(NULL, 0, "%s/d-%0*d", current[i], append, j);
                                newpool[newnames_len] = calloc(1, 1+len);
                                snprintf(newpool[newnames_len], 1+len, "%s/d-%0*d", current[i], append, j);

                                directorypool[dirpool_idx] = calloc(1, 1+len);
                                snprintf(directorypool[dirpool_idx], 1+len, "%s/d-%0*d", current[i], append, j);
                                dirpool_idx++;
                                newnames_len++;
                        }
                }


		//iterate through directories in the previous depth(stored in current), append "f-j" to current[i] and add to filepool
                for(int i = 0; i < size; i++){
                        for(int j = 0; j < filecount; j++){
                                char *newname;
				append = max_name_len - 2;
                                size_t len = snprintf(NULL, 0, "%s/f-%0*d", current[i], append, j);

                                filepool[filepool_idx] = calloc(1, 1+len);
                                snprintf(filepool[filepool_idx], 1+len, "%s/f-%0*d", current[i], append, j);
                                filepool_idx++;
                        }
                }
	        if(pool_depth == 1){
        	        return;
	        }

        	dfs(directorycount, filecount, pool_depth-1, max_name_len, newpool, newnames_len);
	}
	
	int getpowsum(int directorycount, int pool_depth){
		int sum = 0;
		int current = 1;
		for(int i = 0; i < pool_depth; i++){
			current *= directorycount;
			sum += current;
		}
		return sum;
	}	

        start_perf_metrics_thread();
        /* Initialize test dirs and files names */

	char *current[100];
	int directorypool_size = 0;
	int filepool_size = 0;
	if( directorycount > 0){
		/*
		Directory pool size  = no. of directories at depth 0 + no. of directories at depth 1 + .....
		= directorycount + (no. of directories at depth 0)*directorycount + (no. of directories at depth 1)*directory count + ...
		= directorycount + directorycount*directorycount + directorycount*directorycount*directorycount + .....

		Similarly, file pool size = no. of files at depth 0 + no. of files at depth 1 + ....
		= filecount + (no. of directories at depth 0)*filecount + (no. of directories at depth 1)*filecount + ...
		= filecount * ( 1 + (no. of directories at depth 0) + (no. of directories at depth 1) + ....) 
		= filecount * (directorypool_size / directorycount);
		*/
		directorypool_size = getpowsum(directorycount, pool_depth);
		filepool_size = filecount * (directorypool_size / directorycount);
	}
	else
		filepool_size = filecount;
	
	//adding 1 for testdir and test.txt
	filepool_size++;
	directorypool_size++;
	
	//TODO: Free memory for file pool and directory pool.
	filepool = (char **) malloc( filepool_size * sizeof(char*));
	directorypool = (char **) malloc( directorypool_size * sizeof(char*));
	size_t len = 0;
	makelog("len is %d", len);
	current[0] = calloc(1, len + 1);

        len = snprintf(NULL, 0, "/test.txt");
        filepool[filepool_idx] = calloc(1, 1+len);
        snprintf(filepool[filepool_idx], 1+len, "/test.txt");
        filepool_idx++;


        len = snprintf(NULL, 0, "/testdir");
        directorypool[dirpool_idx] = calloc(1, 1+len);
        snprintf(directorypool[dirpool_idx], 1+len, "/testdir");
        dirpool_idx++;

	if( pool_depth > 0) 
		dfs(directorycount, filecount, pool_depth, max_name_len, current, 1);
	
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
