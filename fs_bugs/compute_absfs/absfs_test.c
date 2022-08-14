#include "absfs_test.h"

char *mp = NULL;
absfs_state_t absfs;

static void compute_abstract_state(const char *basepath,
    absfs_state_t state)
{
    absfs_t absfs;

    absfs.hash_option = absfs_hash_method;
    init_abstract_fs(&absfs);
    scan_abstract_fs(&absfs, basepath, false, submit_error);
    memcpy(state, absfs.state, sizeof(absfs_state_t));
    destroy_abstract_fs(&absfs);
}

char *get_abstract_state(const char *basepath,
    absfs_state_t state)
{
    compute_abstract_state(basepath, state);
    char abs_state_str[33] = {0};
    char *strp = abs_state_str;
    for (int i = 0; i < 16; ++i) {
        size_t res = snprintf(strp, 3, "%02x", absfs[0][i]);
        strp += res;
    }
    return abs_state_str;
}

int main(int argc, char *argv[])
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <mountpoint>\n", argv[0]);
        exit(1);
    }
    mp = argv[1];
    absfs = calloc(1, sizeof(absfs_state_t));

    char *absfs_ret = compute_abstract_state(mp, absfs);
    printf("%s\n", absfs_ret);

    free(absfs);
    return 0;
}
