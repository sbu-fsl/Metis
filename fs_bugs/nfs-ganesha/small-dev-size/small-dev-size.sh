#!/bin/bash

SERVER_MNT_DIR="/mnt/test-nfs-ganesha-export"
CLIENT_MNT_DIR="/mnt/test-nfs-ganesha-ext4-i0-s0"
EXT4_RAMDISK="/dev/ram0"
BRD_SIZE=1331 # in KiB

# Unload brd ramdisk kernel module
if lsmod | grep -q "^brd"; then
    echo "brd module is loaded. Unloading it now."
    if rmmod brd; then 
        echo "Successfully removed brd module."
    else
        echo "Failed to remove brd module."
        exit 1
    fi
fi

# Create a small ramdisk with 256KiB
if modprobe brd rd_size=$BRD_SIZE; then
    echo "Successfully loaded brd module."
else
    echo "Failed to load brd module."
    exit 1
fi

# Check if the mount point is already mounted, unmount it
if test -n "$(mount | grep $SERVER_MNT_DIR)" ; then
    umount $SERVER_MNT_DIR || exit $?
fi

# Check if the mount point is already mounted, unmount it
if test -n "$(mount | grep $CLIENT_MNT_DIR)" ; then
    umount $CLIENT_MNT_DIR || exit $?
fi

# Remove mount point if not created, and create it again
if test -d $SERVER_MNT_DIR ; then
    rm -r $SERVER_MNT_DIR
fi

# Remove mount point if not created, and create it again
if test -d $CLIENT_MNT_DIR ; then
    rm -r $CLIENT_MNT_DIR
fi

# Create mount points and set permissions
mkdir -p $SERVER_MNT_DIR || { echo "Failed to create directory $SERVER_MNT_DIR"; exit $?; }
mkdir -p $CLIENT_MNT_DIR || { echo "Failed to create directory $CLIENT_MNT_DIR"; exit $?; }
chmod 755 $SERVER_MNT_DIR || { echo "Failed to set permissions for $SERVER_MNT_DIR"; exit $?; }
chmod 755 $CLIENT_MNT_DIR || { echo "Failed to set permissions for $CLIENT_MNT_DIR"; exit $?; }

# Create an Ext4 filesystem on the ramdisk
mkfs.ext4 $EXT4_RAMDISK || { echo "Failed to create Ext4 filesystem on $EXT4_RAMDISK"; exit $?; }
mount $EXT4_RAMDISK $SERVER_MNT_DIR || { echo "Failed to mount $EXT4_RAMDISK on $SERVER_MNT_DIR"; exit $?; }

# Start NFS-Ganesha server
systemctl start nfs-ganesha 

# Mount the NFS-Ganesha export on the client
mount.nfs4 -o vers=4 127.0.0.1:$SERVER_MNT_DIR $CLIENT_MNT_DIR

# Using "df -h" or a C program (statfs) to check the size of the mounted filesystem 
df -h
#make
#./ganesha-small-dev

umount $CLIENT_MNT_DIR

dbus-send --system --type=method_call --print-reply --dest=org.ganesha.nfsd /org/ganesha/nfsd/ExportMgr org.ganesha.nfsd.exportmgr.RemoveExport uint16:77 

umount $SERVER_MNT_DIR

systemctl stop nfs-ganesha
