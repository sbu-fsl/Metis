/*
 * Copyright (c) 2020-2024 Yifei Liu
 * Copyright (c) 2020-2024 Wei Su
 * Copyright (c) 2020-2024 Erez Zadok
 * Copyright (c) 2020-2024 Stony Brook University
 * Copyright (c) 2020-2024 The Research Foundation of SUNY
 *
 * You can redistribute it and/or modify it under the terms of the Apache
 * License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
 */

#include "fileutil.h"
#include <sys/wait.h>

#define MP_PREFIX "/mnt/test-"
// TODO: MUST BE FULL PATH FOR GANESHA LOG/CONF FILE, NEED TO FIGURE OUT WHY

static void execute_cmd(const char *cmd)
{
    int retval = system(cmd);
    int status, signal = 0;
    if ((status = WEXITSTATUS(retval)) != 0) {
        fprintf(stderr, "Command `%s` failed with %d.\n", cmd, status);
    }
    if (WIFSIGNALED(retval)) {
        signal = WTERMSIG(retval);
        fprintf(stderr, "Command `%s` terminated with signal %d.\n", cmd,
                signal);
    }
    if (status || signal) {
        exit(1);
    }
}

int execute_cmd_status(const char *cmd)
{
    if (cmd == NULL) {
        return -1;  // Or another error handling code if cmd is NULL
    }

    int retval = system(cmd);

    if (retval == -1) {
        return -1;  // System call failed
    } else if (WIFEXITED(retval)) {
        return WEXITSTATUS(retval);  // Return the exit status of the command
    }
    return -2;  // Indicate abnormal termination, could use a different error code
}

static int is_mounted(const char *path) {
    char command[256];
    snprintf(command, sizeof(command), "mountpoint -q \"%s\"", path);
    // Executes the command. 
    // If the directory is a mountpoint, the command returns 0, else non-zero.
    return system(command) == 0;
}

static int check_device(const char *devname, const size_t exp_size_kb)
{
    int fd = open(devname, O_RDONLY);
    struct stat devinfo;
    if (fd < 0) {
        fprintf(stderr, "Cannot open %s (err=%s, %d)\n",
                devname, errnoname(errno), errno);
        return -errno;
    }
    int retval = fstat(fd, &devinfo);
    if (retval < 0) {
        fprintf(stderr, "Cannot stat %s (err=%s, %d)\n",
                devname, errnoname(errno), errno);
        close(fd);
        return -errno;
    }
    if (!S_ISBLK(devinfo.st_mode)) {
        fprintf(stderr, "%s is not a block device.\n", devname);
        close(fd);
        return -ENOTBLK;
    }
    size_t devsize = fsize(fd);
    if (devsize < exp_size_kb * 1024) {
        fprintf(stderr, "%s is smaller than expected (expected %zu KB, "
                "got %zu).\n", devname, exp_size_kb, devsize / 1024);
        close(fd);
        return -ENOSPC;
    }
    close(fd);
    return 0; 
}

static int setup_generic(const char *fsname, const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    ret = check_device(devname, size_kb);
    if (ret != 0) {
        fprintf(stderr, "Cannot setup %s because %s is bad or not ready.\n",
                fsname, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
            "dd if=/dev/zero of=%s bs=1k count=%zu status=none",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.%s %s", fsname, devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_mtd(const size_t size_kb)
{
    char cmdbuf[PATH_MAX];

    snprintf(cmdbuf, PATH_MAX, "mtdram total_size=%ld erase_size=16", size_kb / 1024);
    execute_cmd(cmdbuf);
    snprintf(cmdbuf, PATH_MAX, "mtdblock");
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_jffs2(const char *devname, const size_t size_kb)
{
    char cmdbuf[PATH_MAX];
    int ret, randnum;
    int failCount = 0;

    // check if mtdram and mtdblock are loaded
    execute_cmd("lsmod | grep mtdram");
    execute_cmd("lsmod | grep mtdblock");

mtd_check:
    // check if the device is ready
    ret = check_device(devname, size_kb);
    if (ret != 0)
    {
        if (failCount > 2)
        {
            fprintf(stderr, "Cannot setup jffs2 because %s is bad or not ready.\n",
                    devname);
            return ret;
        }
        else
        {
            failCount++;
            setup_mtd(size_kb);
            goto mtd_check;
        }
    }
    // create an empty jffs2 image
    // first prepare an empty directory
    srand(time(0));
    randnum = rand() % 65536;
    snprintf(cmdbuf, PATH_MAX, "mkdir -p /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    // make the jffs2 image according to the empty directory created
    snprintf(cmdbuf, PATH_MAX, "mkfs.jffs2 --pad=%zu --root=/tmp/_empty_dir_%d"
                               " -o /tmp/jffs2_%d.img",
             size_kb * 1024, randnum, randnum);
    execute_cmd(cmdbuf);
    // write the image to the mtd block device
    snprintf(cmdbuf, PATH_MAX, "dd if=/tmp/jffs2_%d.img of=%s bs=1k count=%zu "
                               "status=none",
             randnum, devname, size_kb);
    execute_cmd(cmdbuf);
    // cleanup
    snprintf(cmdbuf, PATH_MAX, "rm -r /tmp/_empty_dir_%d", randnum);
    execute_cmd(cmdbuf);
    snprintf(cmdbuf, PATH_MAX, "rm /tmp/jffs2_%d.img", randnum);
    execute_cmd(cmdbuf);
    return 0;
}

static void populate_mountpoints()
{
    char check_mount_cmdbuf[PATH_MAX];
    char unmount_cmdbuf[PATH_MAX];
    char check_mp_exist_cmdbuf[PATH_MAX];
    char rm_mp_cmdbuf[PATH_MAX];
    char mk_mp_cmdbuf[PATH_MAX];
    for (int i = 0; i < get_n_fs(); ++i) {
        snprintf(check_mount_cmdbuf, PATH_MAX, "mount | grep %s", get_basepaths()[i]);    
        /* If the mountpoint has fs mounted, then unmount it */
        if (execute_cmd_status(check_mount_cmdbuf) == 0) {
            snprintf(unmount_cmdbuf, PATH_MAX, "umount -f %s", get_basepaths()[i]);
            execute_cmd(unmount_cmdbuf);
        }
        /* 
         * Caveat: if we use file/dir pools and test in-memory file systems
         * like VeriFS, we should not remove the mount point here because
         * we need to pre-create files/dirs in the pool. Removing mountpoints
         * simply erase the precreated files/dirs.
         *
         * Also, we cannot mount VeriFS and other in-memory file systems on
         * a non-empty mount point.
         * 
         * The correct way would be removing and recreating mount point of 
         * VeriFS in the setup shell scripts before running pan.
         */

        snprintf(mk_mp_cmdbuf, PATH_MAX, "mkdir -p %s", get_basepaths()[i]);
        execute_cmd(mk_mp_cmdbuf);
    }
}

static int setup_f2fs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 38 MiB
    ret = check_device(devname, 38 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.f2fs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_btrfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB (must mkfs.btrfs with -M option)
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.btrfs -M -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_xfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.xfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_jfs(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 16 MiB
    ret = check_device(devname, 16 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.jfs -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

static int setup_nilfs2(const char *devname, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    // Expected >= 1028 KiB
    ret = check_device(devname, 1028);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=%zu count=1",
             devname, size_kb * 1024);
    execute_cmd(cmdbuf);
    // format the device with the specified file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.nilfs2 -B 16 -f %s", devname);
    execute_cmd(cmdbuf);

    return 0;
}

int start_nfs_ganesha_server(int idx) {
    int ret = -1;
    int retry_limit = 10;
    bool has_failure = false;
    char cmdbuf[PATH_MAX];

    /* Remember to do "systemctl enable nfs-ganesha" first
     * This step also exports the server path
     */
    snprintf(cmdbuf, PATH_MAX, "systemctl restart nfs-ganesha");
    execute_cmd(cmdbuf);

check_server_status:
    ret = execute_cmd_status("rpcinfo -u localhost nfs");
    if (ret != 0) {
        /* If unmounting failed due to device being busy, again up to
            * retry_limit times with 100 * 2^n ms (n = num_retries) */
        useconds_t waitms = (1 << (10 - retry_limit));
        if (retry_limit > 0) {
            fprintf(stderr, "NFS-ganesha server not started. Checking status after %dms.\n", waitms);
            usleep(1000 * waitms);
            retry_limit--;
            goto check_server_status;
        }
        fprintf(stderr, "Could not start NFS-Ganesha-server %s at %s (%s)\n",
                get_fslist()[idx], get_basepaths()[idx], errnoname(errno));
        has_failure = true;
    }

    if (has_failure)
        return -1;

    return 0;
}

int export_nfs_server(int idx) {
    int ret = -1;
    char cmdbuf[PATH_MAX];
    // Export the kernel NFS server path 
    snprintf(cmdbuf, PATH_MAX, "exportfs -o rw,sync,no_root_squash %s:%s", 
        NFS_LOCALHOST, NFS_EXPORT_PATH);
    ret = execute_cmd_status(cmdbuf);
    if (ret != 0) {
        fprintf(stderr, "Failed to export kernel NFS server path %s for file system %s.\n", 
            NFS_EXPORT_PATH, get_fslist()[idx]);
        return -2;
    }
    return 0;
}

static int start_nfs_server()
{
    int ret = -1;
    char cmdbuf[PATH_MAX];

    // Remember to do "systemctl enable nfs-kernel-server" first
    /* TODO: No need to restart nfs-kernel-server every time while
     * mounting, we should only do export and unexport 
     */

    snprintf(cmdbuf, PATH_MAX, "systemctl restart nfs-kernel-server");
    ret = execute_cmd_status(cmdbuf);
    if (ret != 0) {
        fprintf(stderr, "Failed to start nfs-kernel-server.\n");
        return -1;
    }
    return 0;
}

static int start_and_export_nfs_server(int idx) {
    if (start_nfs_server() != 0) {
        return -1;
    }
    // Export NFS server path
    return export_nfs_server(idx);
}

static int setup_nfs_or_ganesha_mountpoints(int fs_idx)
{
    /* Clean up any Genesha resources */
    // Make sure the export path is created 
    // Ganesha client mount directory should be created in populate_mountpoints()
    struct stat st;
    const char *export_path = NULL;
    /* NFS-Ganesha */
    if (is_nfs_ganesha(get_fslist()[fs_idx])) {
        export_path = NFS_GANESHA_EXPORT_PATH;
    }
    /* Kernel NFS */
    else {
        export_path = NFS_EXPORT_PATH;
    }

    if (stat(export_path, &st) == -1) {
        if (mkdir(export_path, 0755) == -1) {
            fprintf(stderr, "Failed to create NFS or NFS-Ganesha export path.\n");
            return -2;
        }
    }
    // Make sure client mount point is not mounted
    // Mount client first, then server
    if (is_mounted(get_basepaths()[fs_idx])) {
        if (umount(get_basepaths()[fs_idx]) == -1) {
            fprintf(stderr, "Failed to unmount NFS or NFS-Ganesha client mount path.\n");
            return -4;
        }
    }
    // Make sure server export directory is not mounted 
    if (is_mounted(export_path)) {
        if (umount(export_path) == -1) {
            fprintf(stderr, "Failed to unmount NFS or NFS-Ganesha export path.\n");
            return -3;
        }
    }
    return 0;
}

/* Setup NFS-Ganesha server and client on the same machine with 
 * an ext4 file system as the backing store
 */
static int setup_nfs_or_ganesha_ext4(int fs_idx, const char *devname, const size_t size_kb)
{
    // Set up NFS-Ganesha server export and client mount paths on the same machine
    int ret = -1;
    char cmdbuf[PATH_MAX];
    ret = setup_nfs_or_ganesha_mountpoints(fs_idx);
    if (ret != 0) {
        return ret;
    }
    // Check export path device: Ext4 device >= 256 KiB and fill the device with zeros
    ret = check_device(devname, 256);
    if (ret != 0) {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);
    // Format the device with ext4 file system
    snprintf(cmdbuf, PATH_MAX, "mkfs.ext4 -F %s", devname);
    execute_cmd(cmdbuf);

    /* There should be NO NFS-Ganesha server running at this point, we 
     * terminated the ganesha.nfsd process/service in the setup.sh script already
     * Start NFS Ganesha with the desired configuration and log files 
     * that are set in /etc/systemd/system/nfs-ganesha.service
     * Let's not start Ganesha server here, but start right after the mount
     * of the Ganesha server export path
     */
    // start_nfs_ganesha_server(fs_idx);
    /* However, if we check nfs-ext4 whose start and export operations are
     * separated, we need to start the server here and export/unexport 
     * before/after each FS operation but don't need to restart nfs-kernel-server
     * every time for an FS operation
     */
    if (is_nfs_ext4(get_fslist()[fs_idx])) {
        return start_nfs_server();
    }

    return 0;
}

static int mount_verifs2(char *mountpoint)
{
    char cmdbuf[PATH_MAX];
    // Max 5 seconds
    const int MAX_WAIT_SECONDS = 5;
    const int MAX_WAIT_TIME = MAX_WAIT_SECONDS * 1000000;
    // wait until refFS is fully setup at mountpoint (when st_dev or st_ino updates at the mountpoint)
    int wait_time = 1; // initial wait time, in microseconds.
    int total_time = 0;
    bool mounted = false;

    if (is_mounted(mountpoint)) {
        snprintf(cmdbuf, PATH_MAX, "umount \"%s\"", mountpoint);
        
        if (execute_cmd_status(cmdbuf) != 0) {
            fprintf(stderr, "Failed to unmount an existing VeriFS2 file system.\n");
            return -1;
        }
    }

    // Remove the mountpoint if it exists and create a new one to remove 
    // all the content inside the mountpoint
    if (strncmp(mountpoint, MP_PREFIX, strlen(MP_PREFIX)) == 0) {
        snprintf(cmdbuf, PATH_MAX, "rm -rf %s", mountpoint);

        if (execute_cmd_status(cmdbuf) != 0) {
            fprintf(stderr, "Failed to remove content in the VeriFS2 mount point during setup.\n");
            return -2;
        }

        if (mkdir(mountpoint, 0755) == -1) {
            fprintf(stderr, "Failed to create the VeriFS2 mount point.\n");
            return -3;
        }
    }
    else {
        fprintf(stderr, "Invalid mountpoint for VeriFS2: %s\n", mountpoint);
        return -4;
    }

    while (total_time < MAX_WAIT_TIME && !mounted) {
        snprintf(cmdbuf, PATH_MAX, "mount -t fuse.fuse-cpp-ramfs verifs2 %s", mountpoint);
        execute_cmd(cmdbuf);

        usleep(wait_time);

        if (is_mounted(mountpoint)) {
            mounted = true;
            break;
        }
        
        total_time += wait_time;
        // wait until next attempt is multiplied by 2, for similar reason to umount() in mount.c
        wait_time = (wait_time > MAX_WAIT_TIME/2) ? MAX_WAIT_TIME : (wait_time * 2);
    }

    if (!mounted){
        fprintf(stderr, "Cannot mount %s , did not setup in time.\n", mountpoint);
        return -5;
    }
    return 0;
}

static int setup_nfs_ganesha_verifs2(int fs_idx)
{
    // Set up NFS-Ganesha server export and client mount paths on the same machine
    int ret = -1;
    char cmdbuf[PATH_MAX];
    ret = setup_nfs_or_ganesha_mountpoints(fs_idx);
    if (ret != 0) {
        return ret;
    }
    // Mount VeriFS2 at the NFS-Ganesha server path
    ret = mount_verifs2(NFS_GANESHA_EXPORT_PATH);
    if (ret != 0) {
        return ret;
    }
    // Start NFS Ganesha service only once here for VeriFS2
    start_nfs_ganesha_server(fs_idx);
    // Mount the NFS-Ganesha client path with the passed get_basepaths()[i]
    snprintf(cmdbuf, PATH_MAX, "mount.nfs4 -o vers=4 %s:%s %s", 
        NFS_GANESHA_LOCALHOST, NFS_GANESHA_EXPORT_PATH, get_basepaths()[fs_idx]);
    ret = execute_cmd_status(cmdbuf);
    if (ret != 0) {
        fprintf(stderr, "Failed to mount NFS-Ganesha client path %s for VeriFS2.\n", get_basepaths()[fs_idx]);
        return -6;
    }
    return 0;
}

static int setup_nfs_verifs2(int fs_idx)
{
    // Set up Kernel NFS server export and client mount paths on the same machine
    int ret = -1;
    char cmdbuf[PATH_MAX];
    ret = setup_nfs_or_ganesha_mountpoints(fs_idx);
    if (ret != 0) {
        return ret;
    }
    // Mount VeriFS2 at the NFS server path
    ret = mount_verifs2(NFS_EXPORT_PATH);
    if (ret != 0) {
        fprintf(stderr, "Failed to mount VeriFS2 at NFS server path %s.\n", NFS_EXPORT_PATH);
        return ret;
    }
    // Start Kernel NFS server service only once here for VeriFS2
    ret = start_and_export_nfs_server(fs_idx);
    if (ret != 0) {
        fprintf(stderr, "Failed to start NFS server for VeriFS2.\n");
        return ret;
    }
    // Mount the kernel NFS client path with the passed get_basepaths()[i]
    /* Note: when we use VeriFS2 for NFSv3, the server export path is 
     * defined as "NFS_EXPORT_PATH". However, when we use VeriFS2 for NFSv4 and
     * specify fsid=0 in /etc/exports, the export point with fsid=0 will be 
     * used as the root of the overall exported filesystem, so the export path in 
     * this case should be "/". If we still use the NFS_EXPORT_PATH for this case,
     * we got error "mount.nfs: mounting localhost:/mnt/test-nfs-export failed, 
     * reason given by server: No such file or directory".
     */
    snprintf(cmdbuf, PATH_MAX, "mount -t nfs -o rw,nolock,vers=4,proto=tcp %s:%s %s", 
        NFS_LOCALHOST, NFS_ROOT_EXPORT_PATH, get_basepaths()[fs_idx]);
    ret = execute_cmd_status(cmdbuf);
    if (ret != 0) {
        fprintf(stderr, "Failed to mount NFS client path %s for VeriFS2.\n", get_basepaths()[fs_idx]);
        return -6;
    }
    return 0;
}

static int setup_verifs1(int i)
{
    char cmdbuf[PATH_MAX];

    snprintf(cmdbuf, PATH_MAX, "crmfs %s", get_basepaths()[i]);
    execute_cmd(cmdbuf);
    return 0;
}

static int setup_verifs2(int i)
{
    char *mountpoint = get_basepaths()[i];
    return mount_verifs2(mountpoint);
}

static int setup_nova(const char *devname, const char *basepath, const size_t size_kb)
{
    int ret;
    char cmdbuf[PATH_MAX];
    //128MiB
    ret = check_device(devname, 128 * 1024);
    if (ret != 0)
    {
        fprintf(stderr, "Cannot %s because %s is bad or not ready.\n",
                __FUNCTION__, devname);
        return ret;
    }
    // fill the device with zeros
    snprintf(cmdbuf, PATH_MAX,
             "dd if=/dev/zero of=%s bs=1k count=%zu",
             devname, size_kb);
    execute_cmd(cmdbuf);

    snprintf(cmdbuf, PATH_MAX, "mount -t NOVA -o init %s %s", devname, basepath);
    ret = execute_cmd_status(cmdbuf);
    if(ret!=0) {
        fprintf(stderr, "Cannot %s because initial mount failed at device: %s\n",
                __FUNCTION__, devname);
        return ret;
    }
    ret = umount2(basepath, 0);    
    return ret;
}
void setup_filesystems()
{
    int ret;
    populate_mountpoints();
    for (int i = 0; i < get_n_fs(); ++i)
    {
        if (strcmp(get_fslist()[i], "jffs2") == 0)
        {
            ret = setup_jffs2(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "f2fs") == 0)
        {
            ret = setup_f2fs(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "btrfs") == 0)
        {
            ret = setup_btrfs(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "xfs") == 0)
        {
            ret = setup_xfs(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "jfs") == 0)
        {
            ret = setup_jfs(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "nilfs2") == 0)
        {
            ret = setup_nilfs2(get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "nova") == 0)
        {
            ret = setup_nova(get_devlist()[i], get_basepaths()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "nfs-ganesha-ext4") == 0 || strcmp(get_fslist()[i], "nfs-ext4") == 0)
        {
            ret = setup_nfs_or_ganesha_ext4(i, get_devlist()[i], get_devsize_kb()[i]);
        }
        else if (strcmp(get_fslist()[i], "nfs-ganesha-verifs2") == 0)
        {
            ret = setup_nfs_ganesha_verifs2(i);
        }
        else if (strcmp(get_fslist()[i], "nfs-verifs2") == 0) {
            ret = setup_nfs_verifs2(i);
        }
        // TODO: we need to consider VeriFS1 and VeriFS2 separately here
        else if (is_verifs(get_fslist()[i]))
        {
            const char *fsname = get_fslist()[i];
            size_t strlen = strnlen(fsname, PATH_MAX);
            switch (fsname[strlen - 1])
            {
            case '1':
                ret = setup_verifs1(i);
                break;
            case '2':
                ret = setup_verifs2(i);
                break;
            default:
                fprintf(stderr, "Unknown VeriFS type: %s\n", fsname);
                exit(1);
            }
        }
        else
        {
            ret = setup_generic(get_fslist()[i], get_devlist()[i], get_devsize_kb()[i]);
        }
        if (ret != 0)
        {
            fprintf(stderr, "Cannot setup file system %s (ret = %d)\n",
                    get_fslist()[i], ret);
            exit(1);
        }
    }
}

int mkdir_p(const char *path, mode_t dir_mode, mode_t file_mode)
{
    const size_t len = strlen(path);
    char _path[PATH_MAX];
    char *p; 

    errno = 0;

    /* Copy string so its mutable */
    if (len > sizeof(_path)-1) {
        errno = ENAMETOOLONG;
        return -1; 
    }   
    strcpy(_path, path);

    bool next_f = false;
    bool next_d = false;
    /* Iterate the string */
    for (p = _path + 1; *p; p++) {
        if (*p == '/') {
            /* Temporarily truncate */
            *p = '\0';
            if (mkdir(_path, dir_mode) != 0) {
                if (errno != EEXIST) {
                    return -1; 
                }
            }
            
            *p = '/';

            if (*(p + 1) == 'f')
                next_f = true;
            else if (*(p + 1) == 'd')
                next_d = true;
        }
    }
    if (next_f) {
        int fd = creat(_path, file_mode);
        if (fd >= 0) {
            close(fd);
        }
        else if (errno != EEXIST) {
            return -1;
        }
    }
    if (next_d) {
        if (mkdir(_path, dir_mode) != 0) {
            if (errno != EEXIST) {
                return -1; 
            }
        }
    }

    return 0;
}
