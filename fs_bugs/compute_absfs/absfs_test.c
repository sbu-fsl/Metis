#include "absfs_test.h"

char *get_abstract_state(const char *basepath,
    unsigned int hash_method, char *abs_state_str)
{
    int ret;
    absfs_t absfs;
    absfs.hash_option = hash_method;
    init_abstract_fs(&absfs);
    ret = scan_abstract_fs(&absfs, basepath, false, printf);

    if (ret) {
        printf("Error occurred when computing absfs...\n");
        return NULL;
    }

    char *strp = abs_state_str;
    for (int i = 0; i < 16; ++i) {
        size_t res = snprintf(strp, 3, "%02x", absfs.state[i]);
        strp += res;
    }
    destroy_abstract_fs(&absfs);
    return abs_state_str;
}

// int main(int argc, char *argv[])
// {
//     char *mp = NULL;
//     // By default it is 2 for MD5 
//     unsigned int hash_option = 2;
//     if (argc > 1) {
//         mp = argv[1];
//         if(argc > 2){
//             hash_option = argv[2][0] - '0';
//             if (hash_option > 3) {
//                 fprintf(stderr, "Hash option not supported.\n");
//             }
//         }
//     }
//     else {
//         fprintf(stderr, "Usage: %s <mountpoint> [hash_option]\n", argv[0]);
//         exit(1);
//     }

//     char *abs_state_str = calloc(33, sizeof(char));
//     char *absfs_ret = get_abstract_state(mp, hash_option, abs_state_str);
//     printf("%s\n", absfs_ret);
//     free(abs_state_str);

//     return 0;
// }
