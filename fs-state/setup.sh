#!/bin/bash

FSLIST=(ext4 ext2 xfs)
LOOPDEVS=()
verbose=0

setup_ext() {
    # First argument is the type of file system (ext2/ext3/ext4)
    fstype=$1;
    # Second arg is the path to file system image
    IMGFILE=$2;
    # Third arg: 1 if requires losetup
    require_losetup=$3;

    if [ "$require_losetup" = "1" ]; then
        # Set up loop device if required
        DEVICE=$(runcmd losetup --show -f $IMGFILE);
        echo "Setup loop device $LOOPDEV to forward $IMGFILE." >&2;
        LOOPDEVS+=("$DEVICE");
    else
        # Otherwise regard f/s image as the device
        DEVICE=$IMGFILE;
    fi

    # Format device
    runcmd mkfs.$fstype $DEVICE >&2;

    # Output is the device name
    echo $DEVICE;
}

setup_ext2() {
    IMGFILE='/tmp/fs-ext2.img';
    BLOCKSIZE=1k
    COUNT=256
    runcmd dd if=/dev/zero of=$IMGFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext2 $IMGFILE 1;
}

unset_ext2() {
    IMGFILE='/tmp/fs-ext2.img';
    runcmd rm -f $IMGFILE;
}

setup_ext4() {
    IMGFILE='/tmp/fs-ext4.img';
    BLOCKSIZE=1k
    COUNT=256
    runcmd dd if=/dev/zero of=$IMGFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext4 $IMGFILE 1;
}

unset_ext4() {
    IMGFILE='/tmp/fs-ext4.img';
    runcmd rm -f $IMGFILE;
}

setup_xfs() {
    IMGFILE="/dev/ram0";
    if ! [ -b $IMGFILE ]; then
        echo "$IMGFILE is not found or is not a block device" >&2;
        echo "Please use 'sudo modprobe brd rd_size=<n_kb>' to setup ramdisks" >&2;
        return 1;
    fi

    ramdisk_sz=$(runcmd blockdev --getsize64 $IMGFILE);
    if [ "$ramdisk_sz" -lt 16777216 ]; then
        echo "XFS's minimum file system size is 16MB." >&2;
        echo "Your ramdisk device ($IMGFILE)'s size is $ramdisk_sz" >&2;
        return 1;
    fi

    runcmd mkfs.xfs -f $IMGFILE >&2;
    echo $IMGFILE;
}

unset_xfs() {
    :
}

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
        unset_$fs;
    done
}

runcmd() {
    if [ $verbose != "0" ]; then
        echo ">>> $@" >&2 ;
    fi
    sleep 0.5;
    $@;
    ret=$?;
    if [ $ret -ne 0 ]; then
        echo "Command '$0' exited with error ($ret)." >&2;
        generic_cleanup;
        exit $ret;
    fi
}

monitor() {
    output='pan_mem_stat.csv';
    counter=0;
    echo "Monitor started.";
    while true; do
        mc_pid=$(pgrep pan);
        if [ -n "$mc_pid" ]; then
            counter=$(expr $counter + 1);
            echo -n "$counter," >> $output;
            cat /proc/$mc_pid/stat | cut -d ' ' --output-delimiter=',' -f 1,2,3,24 >> $output;
        fi
        sleep 1;
    done
}

runcmd losetup -D

for fs in ${FSLIST[@]}; do

    # Run individual file system setup scripts defined above
    DEVICE=$(setup_$fs);

    # Mount
    if [ "$(mount | grep /mnt/test-$fs)" ]; then
        runcmd umount -f /mnt/test-$fs;
    fi
    if [ -d /mnt/test-$fs ]; then
        runcmd rm -rf /mnt/test-$fs;
    fi
    runcmd mkdir -p /mnt/test-$fs;

    # echo -n "Confirm >>>"; read;
    echo "Mounting $DEVICE on /mnt/test-$fs";
    runcmd mount -t $fs -o sync,noatime $DEVICE /mnt/test-$fs

    # echo -n "Confirm >>>"; read;
done

# Run test program
runcmd make
echo 'Running file system checker...';
echo 'Please check stdout in output.log, stderr in error.log';
monitor &
./pan 2>error.log > output.log

generic_cleanup;

