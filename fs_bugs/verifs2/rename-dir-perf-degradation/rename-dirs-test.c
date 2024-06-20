#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <linux/limits.h>
#include <errno.h>
#include <string.h>

const char *ext4_fs = "/mnt/ext4-rename-test";
const char *verifs2_fs = "/mnt/verifs2-rename-test";

void perform_rename(const char *src, const char *dst) {
    char ext4_src_path[PATH_MAX], ext4_dst_path[PATH_MAX];
    char verifs2_src_path[PATH_MAX], verifs2_dst_path[PATH_MAX];
    int ext4_ret = 0, ext4_err = 0;
    int verifs2_ret = 0, verifs2_err = 0;
    errno = 0;

    snprintf(ext4_src_path, sizeof(ext4_src_path), "%s/%s", ext4_fs, src);
    snprintf(ext4_dst_path, sizeof(ext4_dst_path), "%s/%s", ext4_fs, dst);

    ext4_ret = rename(ext4_src_path, ext4_dst_path);
    ext4_err = errno;
    
    errno = 0;
    snprintf(verifs2_src_path, sizeof(verifs2_src_path), "%s/%s", verifs2_fs, src);
    snprintf(verifs2_dst_path, sizeof(verifs2_dst_path), "%s/%s", verifs2_fs, dst);

    verifs2_ret = rename(verifs2_src_path, verifs2_dst_path);
    verifs2_err = errno;

    if (ext4_ret == -1 && verifs2_ret == -1) {
        if (ext4_err == verifs2_err) {
            printf("Both failed with error %d: %s\n", ext4_err, strerror(ext4_err));
        } else {
            printf("Error mismatch: ext4: %d (%s), verifs2: %d (%s)\n", ext4_err, strerror(ext4_err), verifs2_err, strerror(verifs2_err));
        }
    } else if (ext4_ret == -1) {
        printf("Ext4 failed with error %d: %s\n", ext4_err, strerror(ext4_err));
    } else if (verifs2_ret == -1) {
        printf("Verifs2 failed with error %d: %s\n", verifs2_err, strerror(verifs2_err));
    } else {
        printf("Both succeeded\n");
    }
}

int main() {

    const char *cases[][2] = {
        {"dir4", "dir5"},                  // Non-existent src, non-existent dst
        {"dir4", "dir3/empty_subdir3"},    // Non-existent src, existent empty dst
        {"dir4", "dir1/filled_subdir1"},   // Non-existent src, existent non-empty dst
    
        {"dir3/empty_subdir3", "dir4"},                   // Existent empty src, non-existent dst
        {"dir3/empty_subdir4", "dir3/empty_subdir5"},     // Existent empty src, existent empty dst
        {"dir3/empty_subdir5", "dir2/filled_subdir2"},    // Existent empty src, existent non-empty dst

        {"dir1/filled_subdir1", "dir5"},                  // Existent non-empty src, non-existent dst
        {"dir1/filled_subdir2", "dir3/empty_subdir5"},    // Existent non-empty src, existent empty dst
        {"dir2/filled_subdir2", "dir2/filled_subdir3"}    // Existent non-empty src, existent non-empty dst
    };

    for (int i = 0; i < 9; i++) {
        perform_rename(cases[i][0], cases[i][1]);
    }

    return 0;
}
