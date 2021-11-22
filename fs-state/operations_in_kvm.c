#include "operations_in_kvm.h"

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>
#include <time.h>

/*
char *base_command = "vmrun -T ws -gu root -gp Pa55word";
char *file_ops_script = "/mnt/hgfs/mcfs_shared/run_file_ops";
char *absfs_script = "/mnt/hgfs/mcfs_shared/run_absfs";
*/


int get_retval_errno(int fsidx, const char *funcname)
{
    char filename[200];
    // scp required
    // scp root@ip:/mnt/mcfs_shared/ret/mcfs_fops_ret /tmp/mcfs_shared/%d/ret/
    char scp_command[500];
    char host_ret_dir[100];
    sprintf(host_ret_dir, "/tmp/mcfs_shared/%d/ret/", fsidx);
    sprintf(scp_command, "scp %s@%s:%s %s", ssh_user, kvmiplist[fsidx], guest_fops_ret_file, host_ret_dir);
    system(scp_command);
    sprintf(filename, "%s/mcfs_fops_ret", host_ret_dir);
    FILE *fptr = fopen(filename, "r");
    if (fptr == NULL)
    {
        fprintf(stderr, "[get_retval_errno] %s file not present in the SCP shared folder %s for command %s\n", filename, kvmiplist[fsidx], funcname);
    }
    int ret = 0, err = 0;
    fscanf(fptr, "%d %d", &ret, &err);
    fclose(fptr);

    errno = err;
    return ret;
}

int create_file_in_kvm(int fsidx, const char *path, int mode)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"create_file %s %d\"", base_command, vmlist[fsidx], file_ops_script, path, mode);
    //ssh root@ip "/bin/bash run_file_ops create_file path mode"
    sprintf(command, "ssh %s@%s \"/bin/bash %s create_file %s %d\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, mode);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int write_file_in_kvm(int fsidx, const char *path, char *data, off_t offset, size_t length)
{
    time_t start = time(NULL);

    char command[10000]; // TODO get appropriate size of the data
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"write_file %s %s %ld %zu\"", base_command, vmlist[fsidx], file_ops_script, path, data, offset, length);
    sprintf(command, "ssh %s@%s \"/bin/bash %s write_file %s %s %ld %zu\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, data, offset, length);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int truncate_file_in_kvm(int fsidx, const char *path, off_t length)
{
    time_t start = time(NULL);
    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"truncate_file %s %ld\"", base_command, vmlist[fsidx], file_ops_script, path, length);
    sprintf(command, "ssh %s@%s \"/bin/bash %s truncate_file %s %ld\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, length);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int unlink_file_in_kvm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"unlink_file %s\"", base_command, vmlist[fsidx], file_ops_script, path);
    sprintf(command, "ssh %s@%s \"/bin/bash %s unlink_file %s\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int create_dir_in_kvm(int fsidx, const char *path, int mode)
{
    time_t start = time(NULL);
    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"create_dir %s %d\"", base_command, vmlist[fsidx], file_ops_script, path, mode);
    sprintf(command, "ssh %s@%s \"/bin/bash %s create_dir %s %d\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, mode);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int remove_dir_in_kvm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"remove_dir %s\"", base_command, vmlist[fsidx], file_ops_script, path);
    sprintf(command, "ssh %s@%s \"/bin/bash %s remove_dir %s\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int freeze_or_thaw_fs_in_kvm(int fsidx, const char *path, unsigned long op)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"freeze_or_thaw_fs %s %lu\"", base_command, vmlist[fsidx], file_ops_script, path, op);
    sprintf(command, "ssh %s@%s \"/bin/bash %s freeze_or_thaw_fs %s %lu\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, op);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int mount_in_kvm(int fsidx, const char *source, const char *target,
    const char *filesystemtype, unsigned long mountflags,
    const char *data)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"mount_fs %s %s %s %lu %s\"", base_command, vmlist[fsidx], file_ops_script, source, target, filesystemtype, mountflags, data);
    sprintf(command, "ssh %s@%s \"/bin/bash %s mount_fs %s %s %s %lu %s\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, source, target, filesystemtype, mountflags, data);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int umount_in_kvm(int fsidx, const char *target, int flags)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"umount_fs %s %d\"", base_command, vmlist[fsidx], file_ops_script, target, flags);
    sprintf(command, "ssh %s@%s \"/bin/bash %s umount_fs %s %d\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, target, flags);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

bool check_file_existence_in_kvm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s fileExistsInGuest %s %s", base_command, vmlist[fsidx], path);
    sprintf(command, "ssh %s@%s \"test -f %s\"", ssh_user, kvmiplist[fsidx], path);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int get_file_from_kvm(int fsidx, const char *path, const char *local_path)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s copyFileFromGuestToHost %s %s %s", base_command, vmlist[fsidx], path, local_path);
    // Copy from guest (path) to host (local_path)
    sprintf(command, "scp %s@%s:%s %s", ssh_user, kvmiplist[fsidx], path, local_path);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int perform_statfs_in_kvm(int fsidx, const char *path)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"get_fs_free_spaces %s\"", base_command, vmlist[fsidx], file_ops_script, path);
    sprintf(command, "ssh %s@%s \"/bin/bash %s get_fs_free_spaces %s\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

size_t get_fs_free_space_in_kvm(int fsidx)
{
    time_t start = time(NULL);

    char filename[100];
    char scp_command[500];
    char host_ret_dir[64];
    sprintf(host_ret_dir, "/tmp/mcfs_shared/%d/ret/", fsidx);
    //sprintf(filename, "/tmp/mcfs_shared/%d/ret/fs_free_space_ret", fsidx);
    sprintf(scp_command, "scp %s@%s:%s %s", ssh_user, kvmiplist[fsidx], guest_fs_free_space_ret_file, host_ret_dir);
    system(scp_command);
    sprintf(filename, "%s/fs_free_space_ret", host_ret_dir);

    FILE *fptr = fopen(filename, "r");
    if (fptr == NULL)
    {
        printf("%s file not found of %s\n", filename, kvmiplist[fsidx]);
    }
    size_t free_spc = -1;
    fscanf(fptr, "%zu", &free_spc);
    fclose(fptr);

    return free_spc;
}

int write_dummy_file_fs_in_kvm(int fsidx, const char *path, size_t fillsz)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"write_dummy_file %s %zu\"", base_command, vmlist[fsidx], file_ops_script, path, fillsz);
    sprintf(command, "ssh %s@%s \"/bin/bash %s write_dummy_file %s %zu\"", ssh_user, kvmiplist[fsidx], guest_file_ops_script, path, fillsz);

    errno = 0;
    system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return get_retval_errno(fsidx, __func__);
}

int take_kvm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "vmrun -T ws snapshot %s %s", vmlist[fsidx], name);
    // virsh snapshot-create-as --domain core-current --name "1"
    sprintf(command, "virsh snapshot-create-as --domain %s --name \"%s\"", kvmlist[fsidx], name);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}

int restore_kvm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char commandRevert[5000];
    //sprintf(commandRevert, "vmrun -T ws revertToSnapshot %s %s", vmlist[fsidx], name);
    // virsh snapshot-revert --domain core-current --snapshotname 1
    sprintf(commandRevert, "virsh snapshot-revert --domain %s --snapshotname %s", kvmlist[fsidx], name);

    errno = 0;
    int ret = system(commandRevert);
    printf("Executed: %s (%lds)\n", commandRevert, (time(NULL) - start));

    if (ret != 0)
    {
        printf("Error while restoring the snapshot %s for kvm %s with revertToSnapshot %d\n", name, kvmlist[fsidx], ret);
        return ret;
    }

    /*
    // Don't need to start after restoration for KVM
    start = time(NULL);
    char commandStart[5000];
    sprintf(commandStart, "vmrun -T ws start %s", vmlist[fsidx]);
    errno = 0;
    ret = system(commandStart);
    if (ret != 0)
    {
        printf("Error while restarting the vm %s after reverting to snapshot %s: %d\n", vmlist[fsidx], name, ret);
    }

    set_env_var_in_kvm(i, "LD_LIBRARY_PATH", "/usr/local/lib");

    printf("Executed: %s (%lds)\n", commandStart, (time(NULL) - start));
    return ret;
    */
}

int delete_kvm_snapshot(int fsidx, const char *name)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "vmrun -T ws deleteSnapshot %s %s", vmlist[fsidx], name);
    // virsh snapshot-delete core-current 1
    sprintf(command, "virsh snapshot-delete %s %s", kvmlist[fsidx], name);

    errno = 0;
    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));  
    return ret;
}

int compute_abstract_state_in_kvm(int fsidx, const char *path, absfs_state_t state)
{
    time_t start = time(NULL);

    char command[5000];
    //sprintf(command, "%s runProgramInGuest %s /bin/bash \"%s\" \"%s\"", base_command, vmlist[fsidx], absfs_script, path);
    sprintf(command, "ssh %s@%s \"/bin/bash %s %s\"", ssh_user, kvmiplist[fsidx], guest_absfs_script, path);
    printf("[YIFEI] compute_abstract_state_in_kvm %d: command to run absfs script in KVM guest: %s\n", fsidx, command);

    errno = 0;
    system(command);

    int ret = get_retval_errno(fsidx, __func__);
    if (ret != 0)
    {
        printf("Could not obtain the abstract state return from guest %s\n", kvmlist[fsidx]);
        return ret;
    }

    char filename[200];
    char scp_command[500];
    char host_ret_dir[100];
    sprintf(host_ret_dir, "/tmp/mcfs_shared/%d/ret/", fsidx);
    sprintf(scp_command, "scp %s@%s:%s %s", ssh_user, kvmiplist[fsidx], guest_absfs_ret_file, host_ret_dir);
    printf("[YIFEI] compute_abstract_state_in_kvm %d: command to copy absfs return file to host machine: %s\n", fsidx, scp_command);

    system(scp_command);

    sprintf(filename, "%s/abstract_fs_ret", host_ret_dir);
    FILE *f = fopen(filename, "r");
    if (f == NULL)
    {
        printf("compute_abstract_state_in_kvm %s not found of %s\n", filename, kvmlist[fsidx]);
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

/*
// Do not need to use this function
int set_env_var_in_kvm(int fsidx, const char *varName, const char *value)
{
    time_t start = time(NULL);

    char command[5000];
    sprintf(command, "%s writeVariable %s guestEnv %s %s", base_command, vmlist[fsidx], varName, value);

    int ret = system(command);

    printf("Executed: %s (%lds)\n", command, (time(NULL) - start));
    return ret;
}
*/