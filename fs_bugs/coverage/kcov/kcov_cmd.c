#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>
#include <linux/types.h>
#include <linux/limits.h>
#include <inttypes.h>

#define KCOV_INIT_TRACE			_IOR('c', 1, unsigned long)
#define KCOV_ENABLE			_IO('c', 100)
#define KCOV_DISABLE			_IO('c', 101)
#define COVER_SIZE			(64<<10)

#define KCOV_TRACE_PC  0
#define KCOV_TRACE_CMP 1

int main(int argc, char **argv)
{
    int fd;
    unsigned long *cover, n, i;

    /* A single fd descriptor allows coverage collection on a single
        * thread.
        */
    fd = open("/sys/kernel/debug/kcov", O_RDWR);
    if (fd == -1)
        perror("open"), exit(1);
    /* Setup trace mode and trace size. */
    if (ioctl(fd, KCOV_INIT_TRACE, COVER_SIZE))
        perror("ioctl"), exit(1);
    /* Mmap buffer shared between kernel- and user-space. */
    cover = (unsigned long*)mmap(NULL, COVER_SIZE * sizeof(unsigned long),
                        PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if ((void*)cover == MAP_FAILED)
        perror("mmap"), exit(1);
    /* Enable coverage collection on the current thread. */
    if (ioctl(fd, KCOV_ENABLE, KCOV_TRACE_PC))
        perror("ioctl"), exit(1);
    /* Reset coverage from the tail of the ioctl() call. */
    __atomic_store_n(&cover[0], 0, __ATOMIC_RELAXED);
    /* That's the target syscal call. */
    read(-1, NULL, 0);
    /* Read number of PCs collected. */
    n = __atomic_load_n(&cover[0], __ATOMIC_RELAXED);
    for (i = 0; i < n; i++) {
        printf("Addr: 0x%lx  --> ", cover[i + 1]);

        FILE *fp;
        char path[1035];
        char cmd_buf[PATH_MAX];
        snprintf(cmd_buf, PATH_MAX, "/usr/bin/addr2line -f -e /mcfs/Linux_Kernel_Install/linux-5.19.9/vmlinux 0x%lx", cover[i + 1]);
        /* Open the command for reading. */
        fp = popen(cmd_buf, "r");
        if (fp == NULL) {
            printf("Failed to run command\n" );
            exit(1);
        }

        /* Read the output a line at a time - output it. */
        while (fgets(path, sizeof(path), fp) != NULL) {
            printf(" %s", path);
        }
        /* close */
        pclose(fp);

    }
    /* Disable coverage collection for the current thread. After this call
        * coverage can be enabled for a different thread.
        */
    if (ioctl(fd, KCOV_DISABLE, 0))
        perror("ioctl"), exit(1);
    /* Free resources. */
    if (munmap(cover, COVER_SIZE * sizeof(unsigned long)))
        perror("munmap"), exit(1);
    if (close(fd))
        perror("close"), exit(1);
    return 0;
}
