#!/bin/bash
  
SERVER_MNT_DIR="/mnt/server";
LOCAL_MNT_DIR="/mnt/local";

EXT4_RAMDISK="/dev/ram1";

setup() {
    if test -n "$(mount | grep $SERVER_MNT_DIR)" ; then
        umount $SERVER_MNT_DIR || exit $?
    fi

    if test -n "$(mount | grep $LOCAL_MNT_DIR)" ; then
        umount $LOCAL_MNT_DIR || exit $?
    fi

    # Remove mount point if not created, and create it again
    if test -d $SERVER_MNT_DIR ; then
        rm -rf $SERVER_MNT_DIR
    fi

    if test -d $LOCAL_MNT_DIR ; then
        rm -rf $LOCAL_MNT_DIR
    fi

    mkdir -p $SERVER_MNT_DIR
    mkdir -p $LOCAL_MNT_DIR
    chmod 755 $SERVER_MNT_DIR
    chmod 755 $LOCAL_MNT_DIR

    if systemctl is-active --quiet nfs-kernel-server; then
    echo "NFS kernel server is already running."
    else
    echo "Starting NFS kernel server..."
    systemctl start nfs-kernel-server
    sleep 20
    echo "NFS kernel server started."
    fi

    MKFS_FLAGS="-F -v -E lazy_itable_init=0,lazy_journal_init=0"
    mkfs.ext4 ${MKFS_FLAGS} $EXT4_RAMDISK || exit $?
}

# Run driver
setup

loop_max=10

for ((i=1; i<=$loop_max; i++)); do
    echo "----- Loop id: $i ----- "
        
    mount -t ext4 $EXT4_RAMDISK $SERVER_MNT_DIR

    exportfs -o rw,sync,no_root_squash localhost:$SERVER_MNT_DIR

    mount -t nfs -o rw,nolock,vers=3,proto=tcp localhost:$SERVER_MNT_DIR $LOCAL_MNT_DIR

    date > $LOCAL_MNT_DIR/date.txt

    umount $LOCAL_MNT_DIR
    exportfs -u localhost:$SERVER_MNT_DIR

    while true; do
    umount $SERVER_MNT_DIR

    if [ $? -eq 0 ]; then
        echo "Unmount succeeded"
        break
    else
        echo "Unmount failed, sleeping for 5 seconds"
        sleep 5
    fi
    done

done