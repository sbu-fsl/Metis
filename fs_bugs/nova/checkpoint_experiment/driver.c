#include "mounts.h"
#include "fileutil.h"
#include "fstestutil.h"
#include "stdlib.h"

void do_checkpoint(const char *devpath, char **bufptr)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t fs_size = fsize(devfd);
	char *buffer, *ptr;

	ptr = mmap(NULL, fs_size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	buffer = malloc(fs_size);
	assert(buffer);

	memcpy(buffer, ptr, fs_size);
	*bufptr = buffer;

	munmap(ptr, fs_size);
	close(devfd);
}

void do_restore(const char *devpath, char *buffer)
{
	int devfd = open(devpath, O_RDWR);
	assert(devfd >= 0);
	size_t size = fsize(devfd);
	char *ptr;

	ptr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, devfd, 0);
	assert(ptr != MAP_FAILED);
	
	memcpy(ptr, buffer, size);
    free(buffer);

	munmap(ptr, size);
	close(devfd);
}

int main(int argc, char *argv[])
{
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <mountpoint>\n", argv[0]);
        exit(1);
    }
    char *mp = NULL;
    char *char_dev = "/dev/pmem0", *blk_dev = "/dev/pmem0", *fs_type = "nova";

    mp = argv[1];

    char cmdbuf[PATH_MAX];
    char lscmdbuf[PATH_MAX];
    // Set up test file and directory pathname
    char test_file[PATH_MAX] = {0};
    char test_dir[PATH_MAX] = {0};
    snprintf(test_file, PATH_MAX, "%s/test.txt", mp);
    snprintf(test_dir, PATH_MAX, "%s/testdir", mp);

    bool is_changed = false;
    int ret = -1;
    int ops_num = -1;

    snprintf(lscmdbuf, PATH_MAX, "ls -lrt %s", mp);
    fprintf(stdout, "Contents of %s before FS creation\n", mp);
    execute_cmd(lscmdbuf);




    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA -o init %s %s", char_dev, mp);
    execute_cmd(cmdbuf);
    fprintf(stdout, "Mounted NOVA file system on %s \n", mp);


    //Create 2 files, and a directory 
    ops_num = 4;
    ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);
    ops_num=0;

    ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);
    snprintf(test_file, PATH_MAX, "%s/test2.txt", mp);
    ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);


    fprintf(stdout, "Contents of %s before unmount\n", mp);
    execute_cmd(lscmdbuf);

    fprintf(stdout, "Unmounting NOVA after creating files\n");
    unmount_fs(mp, fs_type);


    fprintf(stdout, "Contents of %s after unmount\n", mp);
    execute_cmd(lscmdbuf);

    char** buffptr = (char**) calloc(1, sizeof(char *));
    do_checkpoint(char_dev, buffptr);
    
    
    
    fprintf(stdout, "Checkpointing done\n");


    //Mount the fs again without init option
    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA %s %s", char_dev, mp);
    fprintf(stdout, "Mounting fs again to change files\n");
    execute_cmd(cmdbuf);
    //Create new file, and delete test2.txt
    ops_num=3; 
    ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);
    ops_num=0;
    snprintf(test_file, PATH_MAX, "%s/test3.txt", mp);    
    ret = randSyscallChanger(ops_num, test_file, test_dir, &is_changed);

    fprintf(stdout, "Contents of %s after changing files\n", mp);
    execute_cmd(lscmdbuf);

    fprintf(stdout, "Files changed, Unmounting NOVA\n");




    unmount_fs(mp, fs_type);
    do_restore(char_dev, *buffptr);
    fprintf(stdout, "Restore done\n");
    //Mount the fs again
    execute_cmd(cmdbuf);

    fprintf(stdout, "Nova mounted after restore\n");    
    fprintf(stdout, "Contents of %s after mounting again\n", mp);
    execute_cmd(lscmdbuf);
    return 0;
}

