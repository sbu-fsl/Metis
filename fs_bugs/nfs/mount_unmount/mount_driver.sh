#!/bin/bash

# This script is used to reproduce busy unmount issue in NFSv4 and NFSv3
# where the NFS server and client are on the same machine

# Pre-defined variables, note that the server and local mount points will be recreated
# Make sure the ramdisk device and directories are not used by other processes or file systems
SERVER_MNT_DIR="/mnt/server"
LOCAL_MNT_DIR="/mnt/local"
EXT4_RAMDISK="/dev/ram0"
SLEEP_SECONDS=5

# Set up device and mount points
setup() {
    # Load brd ramdisk kernel module
    if lsmod | grep -q "^brd"; then
        echo "brd module is loaded. Unloading it now."
        if rmmod brd; then 
            echo "Successfully removed brd module."
        else
            echo "Failed to remove brd module."
            exit 1
        fi
    fi

    # Load brd module with 256 KiB ramdisk size 
    if modprobe brd rd_size=256; then
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
    if test -n "$(mount | grep $LOCAL_MNT_DIR)" ; then
        umount $LOCAL_MNT_DIR || exit $?
    fi

    # Remove mount point if not created, and create it again
    if test -d $SERVER_MNT_DIR ; then
        rm -rf $SERVER_MNT_DIR
    fi

    # Remove mount point if not created, and create it again
    if test -d $LOCAL_MNT_DIR ; then
        rm -rf $LOCAL_MNT_DIR
    fi

    # Create mount points and set permissions
    mkdir -p $SERVER_MNT_DIR || { echo "Failed to create directory $SERVER_MNT_DIR"; exit $?; }
    mkdir -p $LOCAL_MNT_DIR || { echo "Failed to create directory $LOCAL_MNT_DIR"; exit $?; }
    chmod 755 $SERVER_MNT_DIR || { echo "Failed to set permissions for $SERVER_MNT_DIR"; exit $?; }
    chmod 755 $LOCAL_MNT_DIR || { echo "Failed to set permissions for $LOCAL_MNT_DIR"; exit $?; }

    # Check if NFS kernel server is running, start it if not
    if systemctl is-active --quiet nfs-kernel-server; then
        echo "NFS kernel server is already running."
    else
        echo "Starting NFS kernel server..."
        systemctl start nfs-kernel-server
        # Sleep for a while to make sure the NFS server is started
        sleep 20
        echo "NFS kernel server started."
    fi

    # Create ext4 file system on ramdisk for the NFS server export path
    MKFS_FLAGS="-F -v -E lazy_itable_init=0,lazy_journal_init=0"
    mkfs.ext4 ${MKFS_FLAGS} $EXT4_RAMDISK || exit $?
}

# Run the setup function
setup

# Loop 10 times to reproduce the unmount EBUSY issue
loop_max=10

for ((i=1; i<=$loop_max; i++)); do
    echo " ---------- Loop ID: $i ---------- "
    
    mount -t ext4 $EXT4_RAMDISK $SERVER_MNT_DIR || exit $?

    exportfs -o rw,sync,no_root_squash localhost:$SERVER_MNT_DIR || exit $?
    # Mount with NFSv4 or NFSv3
    mount -t nfs -o rw,nolock,vers=4,proto=tcp localhost:$SERVER_MNT_DIR $LOCAL_MNT_DIR || exit $?

    date > $LOCAL_MNT_DIR/date.txt || exit $?

    umount $LOCAL_MNT_DIR || exit $?
    exportfs -u localhost:$SERVER_MNT_DIR || exit $?

    # Try to unmount, if EBUSY, sleep for 5 seconds and try again
    total_sleep=0
    while true; do
        # Expected to have "target is busy" error here
        umount $SERVER_MNT_DIR 

        if [ $? -eq 0 ]; then
            echo "Unmount succeeded with $total_sleep seconds of sleep."
            break
        else
            echo "Unmount failed, sleeping for 5 seconds..."
            total_sleep=$((total_sleep+SLEEP_SECONDS))
            sleep $SLEEP_SECONDS
        fi
    done

done
