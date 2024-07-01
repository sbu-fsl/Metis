#!/bin/bash

NFS_EXPORT_DIR="/mnt/test-nfs-export"
NFS_VERIFS2_CLIENT_DIR="/mnt/test-nfs-verifs2-i0-s0"

# Setup mount point for both NFS server and client
# Unmount and recreate NFS client mount point
if test -n "$(mount | grep $NFS_VERIFS2_CLIENT_DIR)" ; then
    umount $NFS_VERIFS2_CLIENT_DIR || exit $?
fi

if test -d $NFS_VERIFS2_CLIENT_DIR ; then
    rm -rf $NFS_VERIFS2_CLIENT_DIR
fi
mkdir -p $NFS_VERIFS2_CLIENT_DIR

# Unexport and stop NFS server after unmounting the client 
exportfs -u localhost:$NFS_EXPORT_DIR 
systemctl stop nfs-kernel-server

# Unmount and recreate NFS server export dir
if test -n "$(mount | grep $NFS_EXPORT_DIR)" ; then
    umount $NFS_EXPORT_DIR || exit $?
fi

if test -d $NFS_EXPORT_DIR ; then
    rm -rf $NFS_EXPORT_DIR
fi
mkdir -p $NFS_EXPORT_DIR

# Start NFS server 
systemctl restart nfs-kernel-server

# Mount export fs before exporting it
mount -t fuse.fuse-cpp-ramfs verifs2 $NFS_EXPORT_DIR

# Export fs
exportfs -o rw,sync,no_root_squash localhost:$NFS_EXPORT_DIR

# Mount NFS client
mount -t nfs -o rw,nolock,vers=3,proto=tcp localhost:$NFS_EXPORT_DIR $NFS_VERIFS2_CLIENT_DIR

# Populate some files in NFS client
date > $NFS_VERIFS2_CLIENT_DIR/date.txt

make
./verifs2-cr 
