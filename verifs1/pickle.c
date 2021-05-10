#include <sys/mman.h>
#include "crmfs.h"

#include "custom_heap.h"

void feed_hash(SHA256_CTX *hashctx, const void *data, size_t len) {
    if (hashctx == NULL)
        return;
    SHA256_Update(hashctx, data, len);
}

size_t write_to_file(int fd, const void *buf, size_t count) {
    errno = 0;
    size_t res = write(fd, buf, count);
    return res;
}

size_t write_and_hash(int fd, SHA256_CTX *hashctx,
                                    const void *data, size_t count) {
    size_t res = write_to_file(fd, data, count);
    feed_hash(hashctx, data, count);
    return res;
}

int verify_file_size(int fd, size_t expected) {
    struct stat info;
    int res = fstat(fd, &info);
    if (res < 0)
        return errno;
    return (info.st_size == expected) ? 0 : -1;
}

int verify_file_integrity(int fd, unsigned char *expected) {
    const size_t blocksize = 4096;
    unsigned char hashres[SHA256_DIGEST_LENGTH] = {0};
    char buf[blocksize];
    SHA256_CTX hashctx;

    int res = SHA256_Init(&hashctx);
    if (res == 0)
        return -2;

    ssize_t readsz;
    while ((readsz = read(fd, buf, blocksize)) > 0) {
        SHA256_Update(&hashctx, buf, readsz);
    }
    if (readsz < 0)
        return errno;

    SHA256_Final(hashres, &hashctx);
    return (memcmp(hashres, expected, SHA256_DIGEST_LENGTH) == 0) ? 0 : -3;
}

/* verify_state_file: Verify the integrity of the state file
 *
 * @param[fd] - File descriptor
 *
 * @return: 0 for success; positive integer for an error number resulted from
 * failed system call; -1 for file size mismatch; -2 for hash error; -3 for
 * mismatch sha256 hash digest.
 */
int verify_state_file(int fd) {
    struct state_file_header header;
    // read the header
    int res = lseek(fd, 0, SEEK_SET);
    if (res < 0)
        return errno;

    ssize_t readsz = read(fd, &header, sizeof(header));
    if (readsz < 0)
        return errno;
    else if (readsz < sizeof(header))
        return ENOSPC;

    // validate if the file size and the size recorded in the header match
    if ((res = verify_file_size(fd, header.fsize)) != 0)
        return res;

    // start reading the whole file and calculating the hash
    if ((res = verify_file_integrity(fd, header.hash)) != 0)
        return res;

    lseek(fd, sizeof(header), SEEK_SET);
    return 0;
}
