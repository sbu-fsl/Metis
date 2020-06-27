#!/bin/bash

RDNUM=1
RDSIZE=10000
MAXPART=2
RAMDISK=/dev/ram0
verbose=0

generic_cleanup() {
    if [ "$(mount | grep '/mnt/test-ramdisk-ext4')" ]; then
        umount -f /mnt/test-ramdisk-ext4;
    fi
    if [ -b "$RAMDISK" ]; then
        rmmod brd
    fi
}

runcmd() {
    if [ $verbose != "0" ]; then
        echo ">>> $@" > /proc/self/fd/2;
    fi
    sleep 0.5;
    $@;
    ret=$?;
    if [ $ret -ne 0 ]; then
        echo "Command '$0' exited with error ($ret)." > /proc/self/fd/2;
        generic_cleanup;
        exit $ret;
    fi
}


# Remove module and all the ramdisks
generic_cleanup;

#Create the ramdisk by adding RAM block module (it will create /dev/ram0 with specific size)
runcmd modprobe brd rd_nr=$RDNUM rd_size=$RDSIZE max_part=$MAXPART

#Create ext4 filesystem to ramdisk
runcmd mkfs.ext4 $RAMDISK

#If point is already mounted, run unmount
if [ "$(mount | grep '/mnt/test-ramdisk-ext4')" ]; then
    runcmd umount -f /mnt/test-ramdisk-ext4;
fi

#If mount point exists, delete it
if [ -d /mnt/test-ramdisk-ext4 ]; then
    runcmd rm -rf /mnt/test-ramdisk-ext4
fi

#Create a new dir as mount point
runcmd mkdir -p /mnt/test-ramdisk-ext4;

#Mount filesystem
runcmd mount -t ext4 -o sync,noatime $RAMDISK /mnt/test-ramdisk-ext4

#Run the test program
runcmd make ramdisk
./pan 2>error.log | tee output.log

#Cleanup
generic_cleanup;