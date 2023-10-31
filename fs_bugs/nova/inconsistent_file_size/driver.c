#include "mounts.h"
#include "fstestutil.h"

char *fs_type = "nova";

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <nova-image> <loop_max>\n", 
            argv[0]);
        exit(1);
    }

    char *mp = NULL, *dev = NULL, *nova_img = NULL;
    mp = argv[1];
    dev = argv[2];
    nova_img = argv[3];
    const long loop_max = atol(argv[4]);

    char test_file[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/d-00/f-02", mp);

    char check_file[PATH_MAX] = {0};
    snprintf(check_file, PATH_MAX, "%s/f-00", mp);

    char test_dir[PATH_MAX] = {0};
    snprintf(test_dir, PATH_MAX, "%s/d-00", mp);

    char cmdbuf[PATH_MAX];
    int ret = -1;
    long loop_id = 0;
    while (loop_id < loop_max) {
        if (loop_id % 100 == 0)
            fprintf(stdout, "loop_id: %ld\n", loop_id);
        // dd the device pmem0
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", nova_img, dev);
        execute_cmd(cmdbuf);

        // Mount the file system
        //mount_fs(dev, mp, fs_type);
        snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", dev, mp);
        execute_cmd(cmdbuf);

        // Write to another file
        bool is_changed = false;
        ret = randSyscallChanger(1, test_file, test_dir, &is_changed);
        if (ret < 0) {
            fprintf(stderr, "Write to %s should not fail.\n", test_file);
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

        if (check_info.st_size != 0) {
            fprintf(stderr, "Nova File Size Not Zero Discrepancy Reproduced!\n");
            exit(1);
        }
        unmount_fs(mp, fs_type);
        //In discrepancy observed, size of /f-00 was 10, but in the checkpointed image it was 0
        //If /f-00 size is observered to be non 0 the discrepancy has been reproduced

        ++loop_id;
    }
    return 0;
}
