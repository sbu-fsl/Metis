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
    while ((r1 = read(fd1, buf1, bs)) > 0 && (r2 = read(fd2, buf2, bs)) > 0) {
        if (memcmp(buf1, buf2, r1) != 0) {
            printf("[%d] cmp_file_content: f1 and f2 content is not equal.\n",
                   cur_pid);
            return 1;
        }
    }
    if (r1 < 0 || r2 < 0) {
        printf("[%d] cmp_file_content: error occurred when reading: %d\n",
               cur_pid, errno);
    }
    return 0;
}

