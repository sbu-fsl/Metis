c_code {
\#include "fileutil.h"

char *fslist[] = {"ext4", "ramfs", "xfs", "nfs"};
#define n_fs 4 
char *basepaths[n_fs];
char *testdirs[n_fs];
char *testfiles[n_fs];

int rets[n_fs], errs[n_fs];
int fds[n_fs] = {-1};
int max_file_descriptor = 2;
};

c_track "func" "9";
c_track "&errno" "sizeof(int)";

proctype worker()
{
    /* Non-deterministic test loop */
    bool eq_of_existence, eq_of_value, eq_of_error, eq_of_content;
    do 
    :: d_step { 
        /* mkdir, check: retval, errno, existence */
        c_code { makelog("BEGIN: mkdir\n"); };
        c_code {
            int i;
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s, %o", mkdir, testdirs[i], 0755);
            }

            Pworker->eq_of_existence = compare_equality_fexists(fslist, n_fs, testdirs);
            Pworker->eq_of_value = compare_equality_values(fslist, n_fs, rets);
            Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);
        };
        assert(eq_of_existence);
        assert(eq_of_value);
        assert(eq_of_error);
        c_code { makelog("END: mkdir\n"); };
    };
    :: d_step { 
        /* rmdir, check: retval, errno, existence */
        c_code { makelog("BEGIN: rmdir\n"); };
        c_code {
            int i;
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", rmdir, testdirs[i]);
            }

            Pworker->eq_of_existence = compare_equality_fexists(fslist, n_fs, testdirs);
            Pworker->eq_of_value = compare_equality_values(fslist, n_fs, rets);
            Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);
        };
        assert(eq_of_existence);
        assert(eq_of_value);
        assert(eq_of_error);
        c_code { makelog("END: rmdir\n"); };
    };
    :: d_step {
        /* open, check: errno, existence */
        c_code { makelog("BEGIN: open\n"); };
        c_code {
	    if( max_file_descriptor < 1022 ){ 
            	int i;
            	for (i = 0; i < n_fs; ++i) {
                	makecall(fds[i], errs[i], "%s, %#x, %o", open, testfiles[i], O_RDWR | O_CREAT, 0644);
            	}
            	Pworker->eq_of_existence = compare_equality_fexists(fslist, n_fs, testdirs);
            	Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);
	    	if(Pworker->eq_of_existence && Pworker->eq_of_error && fds[0]>=0){
	        	max_file_descriptor += n_fs;
			printf("MAX FILE DESCRIPTOR %d\n",max_file_descriptor);
	    	}
	    }
	    else{
		printf("FILE DESCRIPTOR= %d , CAN'T ALLOCATE MORE FILE DESCRIPTORS\n", max_file_descriptor);
	    	Pworker->eq_of_existence = 1;
		Pworker->eq_of_error = 1;
	    }
        };
        assert(eq_of_existence);
        assert(eq_of_error);
        c_code { makelog("END: open\n"); };
    };
    :: d_step {
        /* write, check: retval, errno, content */
        c_code { makelog("BEGIN: write\n"); };
        c_code {
            size_t writelen = pick_value(4096, 16384);
            char *data = malloc(writelen);
            int i;
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d, %p, %zu", write, fds[i], data, writelen);
            }

            free(data);
            Pworker->eq_of_value = compare_equality_values(fslist, n_fs, rets);
            Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);
            Pworker->eq_of_content = compare_equality_fcontent(fslist, n_fs, testfiles, fds);
        };
        assert(eq_of_value);
        assert(eq_of_error);
        assert(eq_of_content);
        c_code { makelog("END: write\n"); };
    };
    :: d_step {
        /* close, check: retval, errno */
        c_code { makelog("BEGIN: close\n"); };
        c_code {
            int i;
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%d", close, fds[i]);
            }
            
            Pworker->eq_of_value = compare_equality_values(fslist, n_fs, rets);
            Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);

	    if(Pworker->eq_of_value && Pworker->eq_of_error && rets[0]>=0){
	        max_file_descriptor -= n_fs;
		printf("MAX FILE DESCRIPTOR %d\n",max_file_descriptor);
	    }
        };
        assert(eq_of_value);
        assert(eq_of_error);
        c_code { makelog("END: close\n"); };
    };
    :: d_step {
        /* unlink, check: retval, errno, existence */
        c_code { makelog("BEGIN: unlink\n"); };
        c_code {
            int i;
            for (i = 0; i < n_fs; ++i) {
                makecall(rets[i], errs[i], "%s", unlink, testfiles[i]);
            }

            Pworker->eq_of_existence = compare_equality_fexists(fslist, n_fs, testdirs);
            Pworker->eq_of_value = compare_equality_values(fslist, n_fs, rets);
            Pworker->eq_of_error = compare_equality_values(fslist, n_fs, errs);
        };
        assert(eq_of_existence);
        assert(eq_of_value);
        assert(eq_of_error);
        c_code { makelog("END: unlink\n"); };
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

            len = snprintf(NULL, 0, "%s/test.txt", basepaths[i]);
            testfiles[i] = calloc(1, len + 1);
            snprintf(testfiles[i], len + 1, "%s/test.txt", basepaths[i]);
        }
    };

    for (i : 1 .. nproc) {
        run worker();
    }

    /* Cleanup */
}

init
{
    run driver(4);
}
