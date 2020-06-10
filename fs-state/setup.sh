#/bin/bash

IMGFILE="fs0.img"
BLOCKSIZE=1k
COUNT=256
verbose=0

generic_cleanup() {
    if [ "$(mount | grep '/mnt/test-ext4')" ]; then
        umount -f /mnt/test-ext4;
    fi
    if [ "$LOOPDEV" ]; then
        losetup -d $LOOPDEV;
    fi
    if [ -f /tmp/$IMGFILE ]; then
        rm -f /tmp/$IMGFILE;
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

# Create disk image file
runcmd dd if=/dev/zero of=/tmp/$IMGFILE bs=$BLOCKSIZE count=$COUNT

# Detach unmounted loop devices
runcmd losetup -D

# Setup loop device
LOOPDEV=$(runcmd losetup --show -f /tmp/$IMGFILE)

# Format the image
runcmd mkfs.ext4 $LOOPDEV

# Mount
if [ "$(mount | grep '/mnt/test-ext4')" ]; then
    runcmd umount -f /mnt/test-ext4;
fi
if [ -d /mnt/test-ext4 ]; then
    runcmd rm -rf /mnt/test-ext4;
    runcmd mkdir -p /mnt/test-ext4;
fi
runcmd mount -t ext4 -o sync,noatime $LOOPDEV /mnt/test-ext4

# Run test program
runcmd make
./pan | tee output.log

generic_cleanup;
