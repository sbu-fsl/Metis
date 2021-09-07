#include "operations_in_vm.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <time.h>

char *base_command = "vmrun -T ws -gu root -gp Pa55word";
char *file_ops_script = "/mnt/hgfs/mcfs_shared/run_file_ops";
char *absfs_script = "/mnt/hgfs/mcfs_shared/run_absfs";

int get_retval_errno(int fsidx, const char *funcname)
{
    char filename[64];
    sprintf(filename, "/tmp/mcfs_shared/%d/ret/mcfs_fops_ret", fsidx);
    FILE *fptr = fopen(filename, "r");
    if (fptr == NULL)
    {
        printf("%s file not present in the shared folder %s for command %s\n", filename, vmlist[fsidx], funcname);
    }
    int ret = 0, err = 0;
    fscanf(fptr, "%d %d", &ret, &err);
    fclose(fptr);

    errno = err;
    return ret;
}

int create_file_in_vm(int fsidx, const char *path, int mode)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"create_file %s %d\"", base_command, vmlist[fsidx], file_ops_script, path, mode);

    errno = 0;
    system(command);
    
    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int write_file_in_vm(int fsidx, const char *path, char *data, off_t offset, size_t length)
{
    time_t start = time(NULL);

    char command[10000]; // TODO get appropriate size of the data
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"write_file %s %s %ld %zu\"", base_command, vmlist[fsidx], file_ops_script, path, data, offset, length);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int truncate_file_in_vm(int fsidx, const char *path, off_t length)
{
    time_t start = time(NULL);
    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"truncate_file %s %ld\"", base_command, vmlist[fsidx], file_ops_script, path, length);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int unlink_file_in_vm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"unlink_file %s\"", base_command, vmlist[fsidx], file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int create_dir_in_vm(int fsidx, const char *path, int mode)
{
    time_t start = time(NULL);
    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"create_dir %s %d\"", base_command, vmlist[fsidx], file_ops_script, path, mode);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int remove_dir_in_vm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"remove_dir %s\"", base_command, vmlist[fsidx], file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int freeze_or_thaw_fs_in_vm(int fsidx, const char *path, unsigned long op)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"freeze_or_thaw_fs %s %lu\"", base_command, vmlist[fsidx], file_ops_script, path, op);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int mount_in_vm(int fsidx, const char *source, const char *target,
    const char *filesystemtype, unsigned long mountflags,
    const char *data)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"mount_fs %s %s %s %lu %s\"", base_command, vmlist[fsidx], file_ops_script, source, target, filesystemtype, mountflags, data);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int umount_in_vm(int fsidx, const char *target, int flags)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"umount_fs %s %d\"", base_command, vmlist[fsidx], file_ops_script, target, flags);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

bool check_file_existence_in_vm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s fileExistsInGuest %s %s", base_command, vmlist[fsidx], path);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int get_file_from_vm(int fsidx, const char *path, const char *local_path)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s copyFileFromGuestToHost %s %s %s", base_command, vmlist[fsidx], path, local_path);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int perform_statfs_in_vm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"get_fs_free_spaces %s\"", base_command, vmlist[fsidx], file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

size_t get_fs_free_space_in_vm(int fsidx)
{
    time_t start = time(NULL);

    char filename[64];
    sprintf(filename, "/tmp/mcfs_shared/%d/ret/fs_free_space_ret", fsidx);
    FILE *fptr = fopen(filename, "r");
    if (fptr == NULL)
    {
        printf("%s file not found of %s\n", filename, vmlist[fsidx]);
    }
    size_t free_spc = -1;
    fscanf(fptr, "%zu", &free_spc);
    fclose(fptr);

    return free_spc;
}

int write_dummy_file_fs_in_vm(int fsidx, const char *path, size_t fillsz)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"write_dummy_file %s %zu\"", base_command, vmlist[fsidx], file_ops_script, path, fillsz);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int take_vm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "vmrun -T ws snapshot %s %s", vmlist[fsidx], name);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int restore_vm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char commandRevert[5000];
    sprintf(commandRevert, "vmrun -T ws revertToSnapshot %s %s", vmlist[fsidx], name);
    errno = 0;
    int ret = system(commandRevert);
    printf("Executed: %s (%lds)\n", commandRevert, (time(NULL) - start));

    if (ret != 0)
    {
        printf("Error while restoring the snapshot %s for vm %s with revertToSnapshot %d\n", name, vmlist[fsidx], ret);
        return ret;
    }

    start = time(NULL);
    char commandStart[5000];
    sprintf(commandStart, "vmrun -T ws start %s", vmlist[fsidx]);
    errno = 0;
    ret = system(commandStart);
    if (ret != 0)
    {
        printf("Error while restarting the vm %s after reverting to snapshot %s: %d\n", vmlist[fsidx], name, ret);
    }

    set_env_var_in_vm(i, "LD_LIBRARY_PATH", "/usr/local/lib");

    printf("Executed: %s (%lds)\n", commandStart, (time(NULL) - start));
    return ret;
}

int delete_vm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "vmrun -T ws deleteSnapshot %s %s", vmlist[fsidx], name);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));  
    return ret;
}

int compute_abstract_state_in_vm(int fsidx, const char *path, absfs_state_t state)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"%s\"", base_command, vmlist[fsidx], absfs_script, path);
    errno = 0;
    system(command);

    int ret = get_retval_errno(fsidx, __func__);
    if (ret != 0)
    {
        printf("Could not obtain the abstract state from guest %s\n", vmlist[fsidx]);
        return ret;
    }

    char filename[64];
    sprintf(filename, "/tmp/mcfs_shared/%d/ret/abstract_fs_ret", fsidx);
    FILE *f = fopen(filename, "r");
    if (f == NULL)
    {
        printf("%s not found of %s\n", filename, vmlist[fsidx]);
    }
    
    unsigned int temp[16];
    for (int i = 0; i < 16; i++)
    {
        fscanf(f, "%02x", &temp[i]);
        state[i] = temp[i];
    }

    fclose(f);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start)); 
    return ret;
}

int set_env_var_in_vm(int fsidx, const char *varName, const char *value)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s writeVariable %s guestEnv %s %s", base_command, vmlist[fsidx], varName, value);

    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

