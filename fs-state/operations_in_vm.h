#include <sys/types.h>
#include <stdbool.h>

#include "abstract_fs.h"
//#include "log.h"

#ifndef _OPERATIONS_IN_VM_H
#define _OPERATIONS_IN_VM_H

int create_file_in_vm(const char *vm, const char *path, int mode);
int write_file_in_vm(const char *vm, const char *path, char *data, off_t offset, size_t length);
int truncate_file_in_vm(const char *vm, const char *path, off_t length);
int unlink_file_in_vm(const char *vm, const char *path);
int create_dir_in_vm(const char *vm, const char *path, int mode);
int remove_dir_in_vm(const char *vm, const char *path);
int freeze_or_thaw_fs_in_vm(const char *vm, const char *path, unsigned long op);
int mount_in_vm(const char *vm, const char *source, const char *target, const char *filesystemtype, unsigned long mountflags, const char *data);
int umount_in_vm(const char *vm, const char *target, int flags);
bool check_file_existence_in_vm(const char *vm, const char *path);
int get_file_from_vm(const char *vm, const char *path, const char *local_path);
int perform_statfs_in_vm(const char *vm, const char *path);
size_t get_fs_free_space_in_vm(const char *vm);
int write_dummy_file_fs_in_vm(const char *vm, const char *path, size_t fillsz);
int take_vm_snapshot(const char *vm, const char *name);
int restore_vm_snapshot(const char *vm, const char *name);
int delete_vm_snapshot(const char *vm, const char *name);
int compute_abstract_state_in_vm(const char *vm, const char *path, absfs_state_t state);
int set_env_var_in_vm(const char *vm, const char *varName, const char *value);

#endif // _OPERATIONS_IN_VM_H
