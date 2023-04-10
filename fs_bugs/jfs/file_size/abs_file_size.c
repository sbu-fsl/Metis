#define _XOPEN_SOURCE 500   /* See feature_test_macros(7) */
#include <ftw.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const char *fs_root = "/mnt/test-ext4";
const char *problem_file = "/mnt/test-ext4/d-00/f-01";

int callback(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf)
{
    // Process the file or directory here
    // printf("%s\n", fpath);
    if (strcmp(fpath, problem_file) == 0) {
        printf("%s\n", fpath);
        printf("file size: %zu\n", sb->st_size);
    }
    else if (strcmp(fpath, fs_root) == 0) {
        printf("%s\n", fpath);
        printf("nlink: %ld\n", sb->st_nlink);
    }

    return 0; // Returning 0 tells nftw() to continue the traversal
}

int main(int argc, char *argv[])
{
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <directory>\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    int result = nftw(argv[1], callback, 10, 0);

    if (result == -1) {
        perror("nftw");
        exit(EXIT_FAILURE);
    }

    exit(EXIT_SUCCESS);
}
