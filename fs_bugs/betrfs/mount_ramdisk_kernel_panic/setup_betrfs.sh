#!/bin/bash

fs=ftfs
BRD_DEVICE=/dev/ram0
BRDMOD="brd"
MNTDIR="/mnt/test-$fs"
BLOCKSIZE=1k
# PLEASE EDIT THE SIZE IN KiB OF RAMDISK IF YOU WANT TO TEST A DIFFERENT SIZE
DEVSZKB=262144

# PLEASE EDIT THE FOLLOWING PARAMETERS TO YOURS
losetup -D
FTFS_DUMMY_DEV=${FTFS_DUMMY_DEV:-$(losetup -f)}
FTFS_PARTITION=/dev/sdc
FTFS_DUMMY_FILE=./dummy.dev
FTFS_KMOD=/home/yifei/betrfs/filesystem/ftfs.ko

setup_ramdisk() {
    DEVICE=$1
    if [ "$(mount | grep $DEVICE)" ]; then
        umount -f $DEVICE
    fi

    if lsmod | grep "$BRDMOD" &> /dev/null ; then
        rmmod $BRDMOD
    fi
    # As we use /dev/ram0, we only need to create one ramdisk
    modprobe brd rd_nr=1 rd_size=$DEVSZKB
    # Zero out the ramdisk
    dd if=/dev/zero of=$DEVICE bs=$BLOCKSIZE count=$DEVSZKB status=none
}

setup_loopdev() {
    dd if=/dev/zero of=$FTFS_DUMMY_FILE bs=$BLOCKSIZE count=$DEVSZKB
    losetup $FTFS_DUMMY_DEV $FTFS_DUMMY_FILE
}

setup_ftfs() {
    # Set up ftfs
    ./mkfs.$fs $FTFS_PARTITION
    insmod $FTFS_KMOD sb_dev=$FTFS_PARTITION sb_fstype=ext4
}

# Create mount point for ftfs
if [ "$(mount | grep $MNTDIR)" ]; then
    umount -f $MNTDIR
fi

if [ -d $MNTDIR ]; then
    rm -rf $MNTDIR
fi
mkdir -p $MNTDIR

if [ "$1" = "loop" ]; then
    # if passed loop as argument, use loop device to mount ftfs
    # sudo mount -t ftfs /dev/loop0 /mnt/test-ftfs -o max=128
    DEVICE=$FTFS_DUMMY_DEV
    setup_loopdev
else
    # Create a ramdisk to mount ftfs
    DEVICE=$BRD_DEVICE
    setup_ramdisk $DEVICE
fi

# mkfs the ftfs partition and insert ftfs module
setup_$fs

# Run C program to constantly mount and unmount ftfs
./mount_betrfs $MNTDIR $DEVICE $fs
