#include "fileutil.h"

int compare_file_content(int fd1, int fd2)
{
    const size_t bs = 4096;
    char buf1[bs], buf2[bs];
    struct stat f1, f2;
    int ret = 0;
    /* Get file properties: Make sure equal file size */
    ret = fstat(fd1, &f1);
    if (ret) {
        printf("[%d] cmp_file_content: fstat f1 failed (%d)\n",
               cur_pid, errno);
        return -1;
    }
    ret = fstat(fd2, &f2);
    if (ret) {
        printf("[%d] cmp_file_content: fstat f2 failed (%d)\n",
               cur_pid, errno);
        return -1;
    }
    if (f1.st_size != f2.st_size) {
        printf("[%d] cmp_file_content: f1 and f2 size differ. "
               "f1 has %zu bytes and f2 has %zu.\n", cur_pid,
               f1.st_size, f2.st_size);
        return 1;
    }
    /* Compare the file content */
    int r1, r2;
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
            printf("[%d] cmp_file_content: f1 and f2 content is not equal.\n",
                   cur_pid);
            return 1;
        }
    }
    lseek(fd1, 0, SEEK_SET);
    lseek(fd2, 0, SEEK_SET);
    if (r1 < 0 || r2 < 0) {
        printf("[%d] cmp_file_content: error occurred when reading: %d\n",
               cur_pid, errno);
    }
    return 0;
}

bool compare_equality_values(char **fses, int n_fs, int *nums)
{
    bool res = true;
    int base = nums[0];
    for (int i = 0; i < n_fs; ++i) {
        if (nums[i] != base) {
            res = false;
            break;
        }
    }
    if (!res) {
        printf("[%d] Discrepancy in return values found:\n", cur_pid);
        for (int i = 0; i < n_fs; ++i)
            printf("[%d] [%s]: %d\n", cur_pid, fses[i], nums[i]);
    }
    return res;
}

bool compare_equality_fexists(char **fses, int n_fs, char **fpaths)
{
    bool res = true;
    bool fexists[n_fs];

    /* Check file existence */
    for (int i = 0; i < n_fs; ++i)
        fexists[i] = check_file_existence(fpaths[i]);

    bool base = fexists[0];
    for (int i = 0; i < n_fs; ++i) {
        if (fexists[i] != base) {
            res = false;
            break;
        }
    }
    if (!res) {
        printf("[%d] Discrepancy in existence of files found:\n", cur_pid);
        for (int i = 0; i < n_fs; ++i) {
            printf("[%d] [%s]: %s: %d\n", cur_pid, fses[i], fpaths[i],
                    fexists[i]);
        }
    }
    return res;
}

bool is_all_fd_invalid(int *fds, int n_fs)
{
    bool res = true;
    for (int i = 0; i < n_fs; ++i) {
        errno = 0;
        /* Stop if any of the fd is valid */
        if (fcntl(fds[i], F_GETFD) != -1) {
            res = false;
            break;
        }
    }
    return res;
}

bool compare_equality_fcontent(char **fses, int n_fs, char **fpaths, int *fds)
{
    bool res = true;

    if (!compare_equality_fexists(fses, n_fs, fpaths))
        return false;

    /* If none of the files exists, return TRUE */
    if (check_file_existence(fpaths[0]) == false)
        return true;

    /* If all fds are not valid, return TRUE */
    if (is_all_fd_invalid(fds, n_fs))
        return true;

    for (int i = 1; i < n_fs; ++i) {
        if (compare_file_content(fds[i-1], fds[i]) != 0) {
            if (res)
                res = false;
            printf("[%d] [%s] (%s) is different from [%s] (%s)\n",
                   cur_pid, fses[i-1], fpaths[i-1], fses[i], fpaths[i]);
        }
    }
    return res;
}

int ls(char* ret_value, char* dir) {
    struct dirent *de;
    DIR *dr = opendir(dir);
   
    if (dr == NULL)  // opendir returns NULL if couldn't open directory
    {
        //printf("Could not open current directory" );
        return -1;
    }

    while ((de = readdir(dr)) != NULL) {
           strcat(ret_value,",");
	   strcat(ret_value,de->d_name);
    }

    closedir(dr);
    return 0;
}

// Creates a 1GB size file for the given path.
int create(char* file) {
	char dd_cmd[strlen(file) + 200];
	strcpy(dd_cmd, "dd if=/dev/zero of=");
	strcpy(dd_cmd, file);
       	strcpy(dd_cmd, " count=1024 bs=1024");
	return system(dd_cmd);
}

int concat(char* file1, char* file2, char* file3) {
   // Open two files to be merged 
   FILE *fp1 = fopen(file1, "r"); 
   FILE *fp2 = fopen(file2, "r");
  
   // Open file to store the result 
   FILE *fp3 = fopen(file3, "w"); 
   char c; 
  
   if (fp1 == NULL || fp2 == NULL || fp3 == NULL) 
   { 
         return -1;
   } 
  
   // Copy contents of first file to merged_file 
   while ((c = fgetc(fp1)) != EOF) 
      fputc(c, fp3); 
  
   // Copy contents of second file to merged_file
   while ((c = fgetc(fp2)) != EOF) 
      fputc(c, fp3); 
  
   fclose(fp1); 
   fclose(fp2); 
   fclose(fp3); 
   return 0;
}

bool compare_filelist(char** filelists, int n_fs) {
    for(int i=1; i < n_fs; i++) {
	    if(strcmp(filelists[0], filelists[i]) != 0)
		    return false;
    }
    return true;
}

void swap(char** val1, char** val2, int n_fs) {
	char* temp[n_fs];
	for(int i=0; i < n_fs; i++) {
	    size_t len = snprintf(NULL, 0, "%s", val1[i]);
            temp[i] = calloc(1, len + 1);
            snprintf(temp[i], len + 1, "%s", val1[i]);
	    strcpy(val1[i], val2[i]);
	    strcpy(val2[i], temp[i]);
	}
}
