#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <string.h>

#include <ftw.h>

#include "errnoname.h"
#include "fileutil.h"
#include "operations.h"
#include "cr.h"
#include "nanotiming.h"
#include "vector.h"
#include "abstract_fs.h"
#include <errno.h>


static void do_pickle_and_load(const char *mp, struct verifs_str *arg) {
    int mpfd = open(mp, O_RDONLY | O_DIRECTORY);
    assert(mpfd >= 0);

    int res = ioctl(mpfd, VERIFS_PICKLE, arg);
    assert(res == 0);

    close(mpfd);

    mpfd = open(mp, O_RDONLY | O_DIRECTORY);
    assert(mpfd >= 0);

    int res1 = ioctl(mpfd, VERIFS_LOAD, arg);
    assert(res1 == 0);

    close(mpfd);
}

int main(int argc, char const *argv[]) {
    // TODO: pass path name via struct verifs_str
    struct verifs_str data;
    strcpy(data.str, "/mnt/data_1.txt");
    do_pickle_and_load("/mnt/test-verifs1", &data);
    return 0;
}
