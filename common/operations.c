#include "operations.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

int create_file(const char *path, int mode)
{
    int fd = creat(path, mode);
    if (fd >= 0) {
        close(fd);
    }
    return (fd >= 0) ? 0 : -1;
}

ssize_t write_file(const char *path, void *data, off_t offset, size_t length)
{
    int fd = open(path, O_RDWR);
    int err;
    if (fd < 0) {
        return -1;
    }
    off_t res = lseek(fd, offset, SEEK_SET);
    if (res == (off_t) -1) {
        err = errno;
        goto exit_err;
    }
    ssize_t writesz = write(fd, data, length);
    if (writesz < 0) {
        err = errno;
        goto exit_err;
    }
    if (writesz < length) {
        fprintf(stderr, "Note: less data written than expected (%ld < %zu)\n",
                writesz, length);
    }
    close(fd);
    return writesz;

exit_err:
    close(fd);
    errno = err;
    return -1;
}

int mv(const char *path1, const char *path2)
{
   fprintf(stderr, "mv called %s %s", path1, path2);
   int ret = rename(path1, path2);
   if ( ret != 0 ){
       fprintf(stderr,"error in rename %d, %d", ret, errno);
       return -1;
   }
   else{
      char cmd[1000] = {0};
    snprintf(cmd, 1000, "ls -lrtha /mnt/test-ext4 >&2");
    int status = system(cmd);
      fprintf(stderr,"no error in rename %d ", status);
   }

   return 0;
}
