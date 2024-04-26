#!/bin/bash
  
SERVER_MNT_DIR="/mnt/server";
LOCAL_MNT_DIR="/mnt/local";

EXT4_RAMDISK="/dev/sdb1";


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

    systemctl restart nfs-kernel-server

    MKFS_FLAGS="-F -v -E lazy_itable_init=0,lazy_journal_init=0"
    mkfs.ext4 ${MKFS_FLAGS} $EXT4_RAMDISK || exit $?
}


# Run driver
setup

#systemctl start nfs-kernel-server
mount -t ext4 $EXT4_RAMDISK /mnt/server

#exportfs -o sync,no_root_squash,rw,insecure,fsid=0 localhost:/
exportfs -o rw,sync,no_root_squash localhost:/mnt/server
mount -t nfs -o rw,sync,vers=3,proto=tcp localhost:/mnt/server /mnt/local
#mount -t nfs4 -o rw,sync localhost:/mnt/server /mnt/local
df -H

date > /mnt/local/date.txt
ls -l /mnt/local
sleep 5

umount /mnt/local
exportfs -v -f -u localhost:/mnt/server
# echo /mnt/server > /proc/fs/nfsd/unlock_filesystem
#systemctl stop nfs-kernel-server
lsof /mnt/server
lsof $EXT4_RAMDISK
fuser -vm /mnt/server
#mount

for i in `seq 1 60`; do
    if umount /mnt/server ; then break; fi
    echo SLEEP 5s, try again...
    #fuser -vm /mnt/server
    sleep 5
done
fuser -vm /mnt/server
df -H
