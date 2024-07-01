#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <errno.h>
#include <string.h>
#include "cr_ioctl.h"

int main() {
    const char *filesystem_path = "/mnt/test-nfs-export";
    const char *client_path = "/mnt/test-nfs-verifs2-i0-s0/test-cr";
    int ckpt_fd = -1, restore_fd = -1;
    int ret;
    size_t key = 100;

    // Open the file system or device
    ckpt_fd = open(filesystem_path, O_RDONLY | __O_DIRECTORY);
    if (ckpt_fd == -1) {
        perror("Failed to open file system for checkpoint");
        exit(EXIT_FAILURE);
    }

    // Perform the checkpoint ioctl operation
    ret = ioctl(ckpt_fd, VERIFS_CHECKPOINT, key);
    if (ret == -1) {
        perror("ioctl checkpoint failed");
        close(ckpt_fd);
        exit(EXIT_FAILURE);
    }

    close(ckpt_fd);
    // Print the result of the ioctl operation
    printf("ioctl checkpoint operation successful\n");

    // Make some changes to the file system
    // Create another file in client_path
    int fd2 = open(client_path, O_CREAT | O_RDWR, 0666);
    if (fd2 == -1) {
        perror("Failed to create file in client path");
        close(ckpt_fd);
        exit(EXIT_FAILURE);
    }
    close(fd2);

    // Restore the file system via 
    restore_fd = open(filesystem_path, O_RDONLY | __O_DIRECTORY);
    if (restore_fd == -1) {
        perror("Failed to open file system for restore");
        exit(EXIT_FAILURE);
    }
    // Perform the restore ioctl operation
    ret = ioctl(restore_fd, VERIFS_RESTORE, key);
    if (ret == -1) {
        perror("ioctl restore failed");
        close(restore_fd);
        exit(EXIT_FAILURE);
    }
    // Close the file descriptor
    close(restore_fd);

    return 0;
}
