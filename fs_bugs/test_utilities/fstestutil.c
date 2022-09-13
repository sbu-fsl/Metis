#include "fstestutil.h"

int randSyscallCreator(int ops_num, char *test_file, char *test_dir)
{
    int ret = -1;
    int offset = 0, writelen = 0, writebyte = 0, filelen = 0;
    switch(ops_num) {
        case 0:
            ret = create_file(test_file, 0644);
            break;
        case 1:
            offset = getRandNum(0, 65536);
            writelen = getRandNum(0, 64409);
            writebyte = getRandNum(1, 255);
            char *data = malloc(writelen);
            generate_data(data, writelen, writebyte);
            ret = write_file(test_file, data, (off_t)offset, (size_t)writelen);
            free(data);
            break;
        case 2:
            filelen = getRandNum(0, 262144);
            ret = truncate(test_file, (off_t)filelen);
            break;
        case 3:
            ret = unlink(test_file);
            break;
        case 4:
            ret = mkdir(test_dir, 0755);
            break;
        case 5:
            ret = rmdir(test_dir);
            break;
        default:
            fprintf(stderr, "Unrecognized ops_num: %d\n", ops_num);
            exit(-1);
    }
    return ret;
}
