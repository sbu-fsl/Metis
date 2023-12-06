#include "mounts.h"
#include "absfs_test.h"
#include "fstestutil.h"
#include <sys/wait.h>

int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

int main(int argc, char **argv)
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <nova-mountpoint> <nova-device>\n", 
            argv[0]);
        exit(1);
    }

    char *nova_mp = NULL, *nova_dev = NULL, *nova_img = NULL,  *ext4_mp = NULL, *ext4_dev = NULL, *ext4_img=NULL;
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

    if(data == NULL) {
         fprintf(stderr, "Failed to malloc while generating data to write");
         exit(1);
    }

    generate_test_data(data, writelen, writebyte);

    // Mount and initialise NOVA
    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA -o init %s %s", nova_dev,nova_mp);
    ret = execute_cmd_status(cmdbuf);
    
    if(ret != 0) {
        fprintf(stderr, "Failed to init mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
        free(data);
        exit(1);
    }

    ret = umount2(nova_mp, 0);
    if( ret != 0) {
    fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
    free(data);
    exit(1);
    }

    while (loop_id < loop_max) {
        fprintf(stdout, "loop_id: %ld\n", loop_id);

        // Mount NOVA
        snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", nova_dev,nova_mp);
        ret = execute_cmd_status(cmdbuf);

        if(ret != 0) {
            fprintf(stderr, "Failed to mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
            free(data);
            exit(1);
        }

        //Unmount NOVA
        ret = umount2(nova_mp, 0);
        if( ret != 0) {
            fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
            free(data);
            exit(1);
       }

        ++loop_id;
    }
    free(data);
    printf("NO DISCREPANCY FOUND, EXITING");
    return 0;
}
