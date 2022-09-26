#include "mounts.h"
#include "fstestutil.h"

#define DEV_SIZE 262144
const size_t bs = 4096;
char *state_ptr = NULL; 
char *fs_type = "jffs2";
char *ckpt_path = "./ckpt_tmp.img";

static inline ssize_t fsize(int fd)
{
    struct stat info;
    int ret = fstat(fd, &info);
    if (ret != 0)
        return -1;
    if (info.st_mode & S_IFREG) {
        return info.st_size;
    } else if (info.st_mode & S_IFBLK) {
        size_t devsz;
        ret = ioctl(fd, BLKGETSIZE64, &devsz);
        if (ret == -1)
            return 0;
        return devsz;
    } else {
        return 0;
    }
}

static void do_checkpoint(const char *devpath, char **bufptr)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t fs_size = fsize(devfd);
	char *buffer, *ptr;

	ptr = mmap(NULL, fs_size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	buffer = malloc(fs_size);
	assert(buffer);

	memcpy(buffer, ptr, fs_size);
	*bufptr = buffer;

	munmap(ptr, fs_size);
	close(devfd);
}

int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <mountpoint> <device> <jffs2-image> <loop_max>\n", 
            argv[0]);
        exit(1);
    }

    char *mp = NULL, *dev = NULL, *jffs2_img = NULL;
    mp = argv[1];
    dev = argv[2];
    jffs2_img = argv[3];
    const long loop_max = atol(argv[4]);

    char test_file[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/test.txt", mp);

    char cmdbuf[PATH_MAX];
    int ret = -1;
    long loop_id = 0;
    while (loop_id < loop_max) {
        if (loop_id % 100 == 0)
            fprintf(stdout, "loop_id: %ld\n", loop_id);
        // dd the device mtdblock0
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", jffs2_img, dev);
        execute_cmd(cmdbuf);

        // Mount the file system
        mount_fs(dev, mp, fs_type);

        // Unlink
        ret = unlink(test_file);
        if (ret < 0) {
            fprintf(stderr, "Unlink should not fail.\n");
            exit(1);
        }

        // Unmount the file system
        unmount_fs(mp, fs_type);

        // Checkpoint the device
        state_ptr = NULL;
        do_checkpoint(dev, &state_ptr);

        // Write checkpoint to disk
        int ckpt_fd = -1;
        ckpt_fd = open(ckpt_path, O_CREAT | O_RDWR | O_TRUNC, 0666);
        if (ckpt_fd < 0) {
            fprintf(stderr, "Cannot create file: %s\n", ckpt_path);
            exit(1);
        }

        size_t remaining = DEV_SIZE;
        char *ptr = state_ptr;
        while (remaining > 0) {
            size_t writelen = (remaining >= bs) ? bs : remaining;
            ssize_t writeres = write(ckpt_fd, ptr, writelen);
            if (writeres < 0) {
                fprintf(stderr, "Cannot write to file: %s\n", ckpt_path);
                close(ckpt_fd);
                exit(1);
            }
            ptr += writeres;
            remaining -= writeres;
        }
        close(ckpt_fd);
        free(state_ptr);

        // dd the checkpoint device
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", ckpt_path, dev);

        // Mount the file system
        mount_fs(dev, mp, fs_type);

        // Check if the file re-appears, if yes, abort the program
        if (access(test_file, F_OK) == 0) {
            fprintf(stderr, "JFFS2 Checkpoint BUG Reproduced!\n");
            unmount_fs(mp, fs_type);
            exit(1);
        }

        // Unmount the file system
        unmount_fs(mp, fs_type);

        ++loop_id;
    }
    return 0;
}
