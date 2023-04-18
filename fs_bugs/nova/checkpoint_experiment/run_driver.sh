#!/bin/bash

#DRIVER_LOOP_MAX=100000

# NOVA parameters
#JFFS2_SIZE=262144
NOVA_MNT_DIR="/mnt/ramdisk"
MTDBLK_DEVICE="/dev/pmem0"

# Set up NOVA
setup_nova() {
    #modprobe mtd
    #modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024) erase_size=16
    #modprobe mtdblock
       

    #Check if NOVA is mounted already, if yes unmount it
    if test -n "$(mount | grep $NOVA_MNT_DIR)" ; then
        umount $NOVA_MNT_DIR || exit $?
    fi


    #Remove mount point if not created, and create it again
    if test -d $NOVA_MNT_DIR ; then
        rm -rf $NOVA_MNT_DIR
    fi
    mkdir -p $NOVA_MNT_DIR

    modprobe nova
    #https://github.com/NVSL/linux-nova/blob/master/Documentation/filesystems/nova.txt (Steps for setting up NOVA)
}

# Run driver
setup_nova

# Usage: ./driver mountpoint
./driver $NOVA_MNT_DIR 

