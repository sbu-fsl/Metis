#!/bin/bash

FSLIST=(ext4 ext2)
LOOPDEVS=()
BLOCKSIZE=1k
COUNT=1024
verbose=0

generic_cleanup() {
    for fs in ${FSLIST[@]}; do
        if [ "$(mount | grep /mnt/test-$fs)" ]; then
            umount -f /mnt/test-$fs;
        fi
    done

    for device in ${LOOPDEVS[@]}; do
        if [ "$device" ]; then
            losetup -d $device;
        fi
    done

    for fs in ${FSLIST[@]}; do
        if [ -f /tmp/fs-$fs.img ]; then
            rm -f /tmp/fs-$fs.img;
        fi
    done
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

for fs in ${FSLIST[@]}; do
    # Create disk image file
    IMGFILE="fs-$fs.img";
    runcmd dd if=/dev/zero of=/tmp/$IMGFILE bs=$BLOCKSIZE count=$COUNT

    # Detach unmounted loop devices
    runcmd losetup -D

    # Setup loop device
    LOOPDEV=$(runcmd losetup --show -f /tmp/$IMGFILE)
    echo "Setup loop device $LOOPDEV to forward /tmp/$IMGFILE.";
    LOOPDEVS+=("$LOOPDEV")

    # Format the image
    runcmd mkfs.$fs $LOOPDEV

    # Mount
    if [ "$(mount | grep /mnt/test-$fs)" ]; then
        runcmd umount -f /mnt/test-$fs;
    fi
    if [ -d /mnt/test-$fs ]; then
        runcmd rm -rf /mnt/test-$fs;
    fi
    runcmd mkdir -p /mnt/test-$fs;

    # echo -n "Confirm >>>"; read;
    runcmd mount -t $fs -o sync,noatime $LOOPDEV /mnt/test-$fs

    # echo -n "Confirm >>>"; read;
done

# Run test program
runcmd make
./pan 2>error.log | tee output.log

generic_cleanup;

