#include "fstestutil.h"

void print_error(char *name) { 
    fprintf(stderr, "%s syscall failed: %s\n", name, strerror(errno)); 
    exit(1);
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <mountpoint>\n", argv[0]);
        exit(1);
    }

    char *mp = NULL;
    mp = argv[1];
    int ret = -1;
    struct stat fileStat;

    // Populate file names
    char test_file[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/file-1", mp);

    char test_link[PATH_MAX] = {0};
    snprintf(test_link, PATH_MAX, "%s/link-1", mp);

    char file_two[PATH_MAX] = {0};
    snprintf(file_two, PATH_MAX, "%s/file-2", mp);

    // create a regular file file-1
    ret = create_file(test_file, O_CREAT|O_WRONLY|O_TRUNC, 0644);
    if (ret < 0) {
        print_error("create_file");
    }
    fprintf(stdout, "[Create file 1]: File created %s\n", test_file);

    // Print file-1 inode number and nlink
    ret = stat(test_file, &fileStat);
    if (ret < 0) {
        print_error("stat-1");
    }    
    fprintf(stdout, "[Stat file 1]: file-1 nlink %ld (ino: %ld)\n", 
        fileStat.st_nlink, fileStat.st_ino);

    // create a hard link link-1 for file-1 
    ret = link(test_file, test_link);
    if (ret < 0) {
        print_error("link");
    }

    ret = stat(test_file, &fileStat);
    if (ret < 0) {
        print_error("stat-2");
    }
    if (fileStat.st_nlink != 2)
        fprintf(stderr, "Error: st_nlink should be 2, not %ld\n", fileStat.st_nlink);

    // create another file: file-2
    ret = create_file(file_two, O_CREAT|O_WRONLY|O_TRUNC, 0644);
    if (ret < 0) {
        print_error("create_file");
    }

    // rename file-2 to link-1
    ret = rename(file_two, test_link);
    if (ret < 0) {
        print_error("rename");
    }

    ret = stat(test_file, &fileStat);
    if (ret < 0) {
        print_error("stat-3");
    }
    if (fileStat.st_nlink != 1)
        fprintf(stderr, "Bug: st_nlink should be 1, not %ld\n", fileStat.st_nlink);    

    return 0;
}
