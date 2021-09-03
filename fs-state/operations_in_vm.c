#include "operations_in_vm.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <time.h>

char *base_command = "vmrun -T ws -gu root -gp Pa55word";

int get_retval_errno(const char *vm, const char *funcname)
{
    clock_t start = clock();
    char command[1000];
    sprintf(command, "%s copyFileFromGuestToHost %s /home/tc/mcfs_fops_ret /home/ubuntu/retfiles/mcfs_fops_ret", base_command, vm);
    system(command);

    FILE *fptr = fopen("/home/ubuntu/retfiles/mcfs_fops_ret", "r");
    if (fptr == NULL)
    {
        printf("Could not obtain the retval file from guest %s for command %s\n", vm, funcname);
    }
    int ret = 0, err = 0;
    fscanf(fptr, "%d %d", &ret, &err);

    fclose(fptr);
    system("rm -rf /home/ubuntu/retfiles/mcfs_fops_ret");

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    errno = err;
    return ret;
}

int create_file_in_vm(const char *vm, const char *path, int mode)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"create_file %s %d\"", base_command, vm, path, mode);

    system(command);
    
    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int write_file_in_vm(const char *vm, const char *path, char *data, off_t offset, size_t length)
{
    clock_t start = clock();

    char command[10000]; // TODO get appropriate size of the data
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"write_file %s '%s' %ld %zu\"", base_command, vm, path, data, offset, length);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int truncate_file_in_vm(const char *vm, const char *path, off_t length)
{
    clock_t start = clock();
    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"truncate_file %s %ld\"", base_command, vm, path, length);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int unlink_file_in_vm(const char *vm, const char *path)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"unlink_file %s\"", base_command, vm, path);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int create_dir_in_vm(const char *vm, const char *path, int mode)
{
    clock_t start = clock();
    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"create_dir %s %d\"", base_command, vm, path, mode);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int remove_dir_in_vm(const char *vm, const char *path)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"remove_dir %s\"", base_command, vm, path);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int freeze_or_thaw_fs_in_vm(const char *vm, const char *path, unsigned long op)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"freeze_or_thaw_fs %s %lu\"", base_command, vm, path, op);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int mount_in_vm(const char *vm, const char *source, const char *target,
    const char *filesystemtype, unsigned long mountflags,
    const char *data)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"mount_fs %s %s %s %lu %s\"", base_command, vm, source, target, filesystemtype, mountflags, data);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int umount_in_vm(const char *vm, const char *target, int flags)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"umount_fs %s %d\"", base_command, vm, target, flags);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

bool check_file_existence_in_vm(const char *vm, const char *path)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s fileExistsInGuest %s %s", base_command, vm, path);

    int ret = system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return ret;
}

int get_file_from_vm(const char *vm, const char *path, const char *local_path)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s copyFileFromGuestToHost %s %s %s", base_command, vm, path, local_path);

    int ret = system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return ret;
}

int perform_statfs_in_vm(const char *vm, const char *path)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"get_fs_free_spaces %s\"", base_command, vm, path);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

size_t get_fs_free_space_in_vm(const char *vm)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s copyFileFromGuestToHost %s /home/tc/fs_free_space /home/ubuntu/retfiles/fs_free_space", base_command, vm);
    system(command);

    FILE *fptr = fopen("/home/ubuntu/retfiles/fs_free_space", "r");
    if (fptr == NULL)
    {
        printf("Could not obtain the freespace file from guest %s\n", vm);
    }
    size_t free_spc = -1;
    fscanf(fptr, "%zu", &free_spc);
    fclose(fptr);
    system("rm -rf /home/ubuntu/retfiles/fs_free_space");

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return free_spc;
}

int write_dummy_file_fs_in_vm(const char *vm, const char *path, size_t fillsz)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_file_ops\" \"write_dummy_file %s %zu\"", base_command, vm, path, fillsz);

    system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return get_retval_errno(vm, __func__);
}

int take_vm_snapshot(const char *vm, const char *name)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "vmrun -T ws snapshot %s %s", vm, name);

    int ret = system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return ret;
}

int restore_vm_snapshot(const char *vm, const char *name)
{
    clock_t start = clock();

    char commandRevert[5000];
    sprintf(commandRevert, "vmrun -T ws revertToSnapshot %s %s", vm, name);
    int ret = system(commandRevert);
    printf("Executed: %s (%fs)\n", commandRevert, ((double)(clock() - start))/CLOCKS_PER_SEC);

    if (ret != 0)
    {
        printf("Error while restoring the snapshot %s for vm %s with revertToSnapshot %d\n", name, vm, ret);
        return ret;
    }

    start = clock();
    char commandStart[5000];
    sprintf(commandStart, "vmrun -T ws start %s", vm);
    ret = system(commandStart);
    if (ret != 0)
    {
        printf("Error while restarting the vm %s after reverting to snapshot %s: %d\n", vm, name, ret);
    }

    set_env_var_in_vm(vm, "LD_LIBRARY_PATH", "/usr/local/lib");

    printf("Executed: %s (%fs)\n", commandStart, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return ret;
}

int delete_vm_snapshot(const char *vm, const char *name)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "vmrun -T ws deleteSnapshot %s %s", vm, name);

    int ret = system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);  
    return ret;
}

int compute_abstract_state_in_vm(const char *vm, const char *path, absfs_state_t state)
{
    clock_t start = clock();

    char command[5000];
    //sprintf(command, "%s runScriptInGuest %s /bin/bash \"/home/tc/absfs %s", base_command, vm, path);
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"/home/tc/run_absfs\" \"%s\"", base_command, vm, path);
    system(command);

    int ret = get_retval_errno(vm, __func__);
    if (ret != 0)
    {
        printf("Could not obtain the abstract state from guest %s\n", vm);
        return ret;
    }
    
    char command2[5000];
    sprintf(command2, "%s copyFileFromGuestToHost %s /home/tc/abstract_fs_ret /home/ubuntu/retfiles/abstract_fs_ret", base_command, vm);
    system(command2);
    FILE *f = fopen("/home/ubuntu/retfiles/abstract_fs_ret", "r");
    if (f == NULL)
    {
        printf("Could NOT obtain the abstract state from guest %s\n", vm);
    }
    
    unsigned int temp[16];
    for (int i = 0; i < 16; i++)
    {
        fscanf(f, "%02x", &temp[i]);
        state[i] = temp[i];
    }

    fclose(f);
    system("rm -rf /home/ubuntu/retfiles/abstract_fs_ret");

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC); 
    return ret;
}

int set_env_var_in_vm(const char *vm, const char *varName, const char *value)
{
    clock_t start = clock();

    char command[5000];
    sprintf(command, "%s writeVariable %s guestEnv %s %s", base_command, vm, varName, value);

    int ret = system(command);

    printf("Executed: %s (%fs)\n", command, ((double)(clock() - start))/CLOCKS_PER_SEC);
    return ret;
}

