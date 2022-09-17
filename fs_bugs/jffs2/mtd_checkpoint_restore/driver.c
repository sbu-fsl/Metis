#include <zlib.h>
#include "mounts.h"
#include "fstestutil.h"

#define SYSCALL_NUM 6
#define BUF_SIZE 4096

typedef unsigned char crc32_state_t[4];

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <fs-type> <loop_max>\n", argv[0]);
        exit(1);
    }
    char *mp = NULL, *dev = NULL, *fs_type = NULL;
    mp = argv[1];
    dev = argv[2];
    fs_type = argv[3];
    const long loop_max = atol(argv[4]);
    // Set up test file and directory pathname
    char test_file[PATH_MAX] = {0};
    char test_dir[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/test.txt", mp);
    snprintf(test_dir, PATH_MAX, "%s/testdir", mp);

    long loop_id = 0;
    int ops_num = 0;
    int ret = 0;
    int sleep_interval;
    ssize_t readsize;
    char buffer[BUF_SIZE] = {0};
    srand(time(NULL));
    // Start the Loop
    while (loop_id < loop_max) {
	    if (loop_id % 100 == 0)
	        fprintf(stdout, "loop_id: %ld\n", loop_id);
        // mount the file system
#ifdef MOUNT_MTD_CHAR
        char cmdbuf[PATH_MAX];
        snprintf(cmdbuf, PATH_MAX, "mount -t jffs2 mtd0 %s", mp);
        execute_cmd(cmdbuf);
#else
        mount_fs(dev, mp, fs_type);
#endif
        // Randomly select an operation
        ops_num = getRandNum(0, SYSCALL_NUM - 1);
        // fprintf(stdout, "ops_num: %d\n", ops_num);
        ret = randSyscallCreator(ops_num, test_file, test_dir);
        // unmount the file system
        unmount_fs(mp, fs_type);
        
        // Checkpoint jffs2 and calculate CRC32
        crc32_state_t state_first, state_second;
        uLong crc32_state_first, crc32_state_second;

        int dev_fd = -1;
        dev_fd = open(dev, O_RDONLY);
        if (dev_fd < 0) {
            fprintf(stderr, "Open dev for first read failed\n");
        }
        while ((readsize = read(dev_fd, buffer, BUF_SIZE)) > 0) {
            ret = (int)
                (crc32_state_first = crc32((uLong) crc32_state_first, (const Bytef *) buffer, 
                                (uInt) readsize));

            memset(buffer, 0, sizeof(buffer));
        }
        if (readsize < 0) {
            fprintf(stderr, "CRC32 Read Error (ret = %d) (err = %d)\n", ret, 
                errno);
            exit(1);
        }
        memcpy(&state_first, &crc32_state_first, sizeof(crc32_state_first));
        close(dev_fd);

        // Sleep a short time
        sleep_interval = getRandNum(0, 1000);
        // fprintf(stdout, "sleep time: %d\n", sleep_interval);
        usleep(sleep_interval);

        // Checkpoint jffs2 and calculate CRC32 again and compare
        dev_fd = open(dev, O_RDONLY);
        if (dev_fd < 0) {
            fprintf(stderr, "Open dev for second read failed\n");
        }
        while ((readsize = read(dev_fd, buffer, BUF_SIZE)) > 0) {
            ret = (int)
                (crc32_state_second = crc32((uLong) crc32_state_second, (const Bytef *) buffer, 
                                (uInt) readsize));

            memset(buffer, 0, sizeof(buffer));
        }
        if (readsize < 0) {
            fprintf(stderr, "CRC32 Read Error (ret = %d) (err = %d)\n", ret, 
                errno);
            exit(1);
        }
        memcpy(&state_second, &crc32_state_second, sizeof(crc32_state_second));
        close(dev_fd);

        if(memcmp(state_first, state_second, sizeof(crc32_state_t)) != 0)
        {
            fprintf(stderr, "Two checkpoint state is NOT equal!\n");
            exit(1);
        }
        
	    ++loop_id;
    }

    return 0;
}
