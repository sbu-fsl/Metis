#include "mounts.h"
#include "fstestutil.h"

char *fs_type = "f2fs";

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <f2fs-image> <loop_max>\n", 
            argv[0]);
        exit(1);
    }

    char *mp = NULL, *dev = NULL, *f2fs_img = NULL;
    mp = argv[1];
    dev = argv[2];
    f2fs_img = argv[3];
    const long loop_max = atol(argv[4]);

    char test_file[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/d-00/f-01", mp);

    char check_file[PATH_MAX] = {0};
    snprintf(check_file, PATH_MAX, "%s/f-02", mp);

    char cmdbuf[PATH_MAX];
    int ret = -1;
    long loop_id = 0;
    while (loop_id < loop_max) {
        if (loop_id % 100 == 0)
            fprintf(stdout, "loop_id: %ld\n", loop_id);

        // dd the device /dev/ram1
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", f2fs_img, dev);
        execute_cmd(cmdbuf);        

        // Mount the file system
        mount_fs(dev, mp, fs_type);

        // Do unlink for /mnt/test-f2fs-i1-s0/d-00/f-01
        ret = unlink(test_file);
        if (ret < 0) {
            fprintf(stderr, "Unlink failed. Error code %d, error: %s\n", 
                errno, strerror(errno));
            exit(1);
        }

        // Check the size of another file
        struct stat check_info;
        ret = stat(check_file, &check_info);
        if (ret != 0) {
            fprintf(stderr, "Cannot stat %s. Error code %d, error: %s\n", 
                check_file, errno, strerror(errno));
            exit(1);
        }

        if (check_info.st_size == 0) {
            fprintf(stderr, "F2FS File Size Zero Discrepany Reproduced!\n");
            exit(1);
        }
        /*
        else {
            fprintf(stderr, "f2 file size: %zu\n", check_info.st_size);
        }
        */

        // Unmount the file system
        unmount_fs(mp, fs_type);

        ++loop_id;
    }
    return 0;
}