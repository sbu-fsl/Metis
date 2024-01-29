#include <stdio.h>
#include <stdlib.h>
#include <sys/mount.h>
#include <sys/wait.h>

int execute_cmd_status(const char *cmd)
{
    int retval = system(cmd);
    int status = WEXITSTATUS(retval);
    return status;
}

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "Usage: %s <nova-mountpoint> <nova-device> <loop-max>\n", 
            argv[0]);
        exit(1);
    }

    char *nova_mp = NULL, *nova_dev = NULL;
    nova_mp = argv[1];
    nova_dev = argv[2];
    int PATH_MAX = 4096;

    const long loop_max = atol(argv[3]);

    char cmdbuf[PATH_MAX];
    
    int ret = -1;
    long loop_id = 0;

    // Mount and initialise NOVA
    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA -o init %s %s", nova_dev,nova_mp);
    ret = execute_cmd_status(cmdbuf);
    
    if(ret != 0) {
        fprintf(stderr, "Failed to init mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
        exit(1);
    }

    ret = umount2(nova_mp, 0);
    if( ret != 0) {
    fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
    exit(1);
    }

    while (loop_id < loop_max) {
        fprintf(stdout, "loop_id: %ld\n", loop_id);

        // Mount NOVA
        snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", nova_dev,nova_mp);
        ret = execute_cmd_status(cmdbuf);

        if(ret != 0) {
            fprintf(stderr, "Failed to mount nova at device=%s mountpoint=%s err:%d", nova_dev, nova_mp, ret);
            exit(1);
        }

        //Unmount NOVA
        ret = umount2(nova_mp, 0);
        if( ret != 0) {
            fprintf(stderr, "Failed to unmount NOVA at mp: %s err:%d", nova_mp, ret);
            exit(1);
       }

        ++loop_id;
    }
    printf("NO DISCREPANCY FOUND, EXITING");
    return 0;
}
