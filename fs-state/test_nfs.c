#include <stdio.h>
#include <errno.h>
#include <unistd.h>

#include <sys/time.h>
#include <nfsc/libnfs.h>

#define MAX_LEN 500

struct nfs_context *nfs = NULL;
struct nfsfh *nfsfh = NULL;

static int init_nfs_context() {
    nfs = nfs_init_context();

    if (nfs == NULL) {
        return errno;
    }

    return 0;
}

int nfs_create_file(const char *path, int mode) {
    int err;

    if (nfs == NULL) {
        err = init_nfs_context();
        if (err < 0) {
            err = errno;
            goto exit_err;
        }
    }

	err = nfs_creat(nfs, path, mode, &nfsfh);
    errno = err;

exit_err:
    return errno;
}

int main(int argc, char const *argv[])
{
    char path[MAX_LEN] = "nfs4://127.0.0.1/source_nfs/test.txt";

    int err = nfs_create_file(path, 0644);

    printf("err val -  %d \n", err);

    return 0;
}
