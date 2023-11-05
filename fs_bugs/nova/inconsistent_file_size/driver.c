#include "mounts.h"
#include "absfs_test.h"
#include "fstestutil.h"

char *fs_type_nova = "nova";
char *fs_type_ext4 = "ext4";



int main(int argc, char **argv)
{
    if (argc < 5) {
        fprintf(stderr, "Usage: %s <nova-mountpoint> <nova-device> <nova-image> <ext4-mountpoint> <ext4-device> <ext4-image> <loop_max>\n", 
            argv[0]);
        exit(1);
    }

    char *nova_mp = NULL, *nova_dev = NULL, *nova_img = NULL,  *ext4_mp = NULL, *ext4_dev = NULL, *ext4_img=NULL;
   unsigned int hash_option = 2; //md5
    nova_mp = argv[1];
    nova_dev = argv[2];
    nova_img = argv[3];

    ext4_mp = argv[4];
    ext4_dev = argv[5];
    ext4_img = argv[6];
    const long loop_max = atol(argv[7]);

    char test_file[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/d-00/f-02", nova_mp);

    char cmdbuf[PATH_MAX];
    int ret = -1;
    long loop_id = 0;

    int offset = 1;
    int writelen = 15;
    int writebyte = getRandNum(1, 255);
    char *data = malloc(writelen);
    generate_test_data(data, writelen, writebyte);

    char *hashname = "md5";

    while (loop_id < loop_max) {
        if (loop_id % 100 == 0)
            fprintf(stdout, "loop_id: %ld\n", loop_id);
        // dd the device pmem0
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", nova_img, nova_dev);
        execute_cmd(cmdbuf);
        snprintf(cmdbuf, PATH_MAX, "dd if=%s of=%s bs=4k status=none", ext4_img, ext4_dev);
        execute_cmd(cmdbuf);

        // Mount NOVA
        snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", nova_dev,nova_mp);
        execute_cmd(cmdbuf);

        //Mount ext4
        mount_fs(ext4_dev, ext4_mp, fs_type_ext4);

        // Write to another file


        snprintf(test_file, PATH_MAX, "%s/d-00/f-02", nova_mp);
        ret = write_file(test_file, O_RDWR, data, (off_t)offset, (size_t)writelen);
        if(ret!=0) {
            fprintf(stderr, "Cannot write to file(NOVA): %s", test_file);
             exit(1);
        }

        snprintf(test_file, PATH_MAX, "%s/d-00/f-02", ext4_mp);
        ret = write_file(test_file, O_RDWR, data, (off_t)offset, (size_t)writelen);
        if(ret!=0) {
            fprintf(stderr, "Cannot write to file(EXT4): %s", test_file);
             exit(1);
        }

        //Check abstract state
        char *nova_abs_state_str = calloc(33, sizeof(char));
        char *nova_absfs_ret = get_abstract_state(nova_mp, hash_option, nova_abs_state_str);

        char *ext4_abs_state_str = calloc(33, sizeof(char));
        char *ext4_absfs_ret = get_abstract_state(ext4_mp, hash_option, ext4_abs_state_str);

        if(strcmp(nova_absfs_ret , ext4_absfs_ret) != 0) {
            fprintf(stderr, "Unequal abstract states for NOVA and ext4\n");
            printf("NOVA HASH: %s\n", nova_abs_state_str);
             printf("EXT4HASH: %s\n", ext4_abs_state_str);
             exit(1);
        }

        free(nova_abs_state_str);
        free(ext4_abs_state_str);

        unmount_fs(nova_mp, fs_type_nova);
        unmount_fs(ext4_mp, fs_type_ext4);
        //In discrepancy observed, size of /f-00 was 10, but in the checkpointed image it was 0
        //If /f-00 size is observered to be non 0 the discrepancy has been reproduced

        ++loop_id;
    }
    free(data);
    return 0;
}
