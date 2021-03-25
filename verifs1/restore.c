#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <errno.h>
#include "errnoname.h"
#include "crmfs.h"

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <mountpoint> <key>\n", argv[0]);
        exit(1);
    }

    const char *mp = argv[1];
    char *end;
    uint64_t key = strtoul(argv[2], &end, 10);
    printf("Restoring file system at %s, key is %lu\n", mp, key);

    int dirfd = open(mp, O_RDONLY | __O_DIRECTORY);
    if (dirfd < 0) {
        fprintf(stderr, "Cannot open %s: %s\n", mp, errnoname(errno));
        exit(1);
    }

    int ret = ioctl(dirfd, VERIFS_RESTORE, (void *)key);
    if (ret != 0) {
        printf("Result: ret = %d, errno = %d (%s)\n",
               ret, errno, errnoname(errno));
    }
    return (ret == 0) ? 0 : 1;
}
