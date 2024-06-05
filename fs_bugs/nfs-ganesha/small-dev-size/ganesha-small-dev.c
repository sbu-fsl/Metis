#include <stdio.h>
#include <sys/vfs.h>

void check_fs_space(const char *path) {
    struct statfs fs;

    if (statfs(path, &fs) == 0) {
        unsigned long long total_size = fs.f_blocks * fs.f_bsize;
        printf("File system: %s\n", path);
        printf("Total size: %llu bytes\n", total_size);
    } else {
        perror("statfs");
    }
}

int main() {
    const char *paths[] = {
        "/mnt/test-nfs-ganesha-export",
        "/mnt/test-nfs-ganesha-ext4-i0-s0"
    };
    int num_paths = sizeof(paths) / sizeof(paths[0]);

    for (int i = 0; i < num_paths; i++) {
        check_fs_space(paths[i]);
    }

    return 0;
}
