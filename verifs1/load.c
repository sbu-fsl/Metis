#include <stdint.h>
#include <errno.h>
#include <mcfs/errnoname.h>
#include "common.h"
#include "cr.h"

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <mountpoint> <output-file>\n", argv[0]);
        exit(1);
    }

    // open the mounting point directory
    int dirfd = open(argv[1], O_RDONLY | __O_DIRECTORY);
    if (dirfd < 0) {
        fprintf(stderr, "Cannot open %s: %s\n", argv[1], errnoname(errno));
        exit(1);
    }

    // write the config file to pass the output file path
    int cfgfd = open(VERIFS_LOAD_CFG, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (cfgfd < 0) {
        fprintf(stderr, "Cannot open/create %s: (%d:%s)\n", VERIFS_LOAD_CFG,
                errno, errnoname(errno));
        exit(2);
    }
    size_t pathlen = strnlen(argv[2], PATH_MAX);
    ssize_t res = write(cfgfd, argv[2], pathlen);
    if (res < 0) {
        fprintf(stderr, "Cannot write parameter to %s: (%d:%s)\n",
                VERIFS_LOAD_CFG, errno, errnoname(errno));
        exit(3);
    }
    close(cfgfd);

    // call the ioctl
    int ret = ioctl(dirfd, VERIFS_LOAD, nullptr);
    if (ret != 0) {
        printf("Result: ret = %d, errno = %d (%s)\n",
               ret, errno, errnoname(errno));
    }
    close(dirfd);
    return (ret == 0) ? 0 : 1;
}
