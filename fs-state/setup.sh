#!/bin/bash

FSLIST=(ext4 ext2 jffs2)
DEVLIST=(/dev/ram0 /dev/ram1 /dev/mtdblock0)
LOOPDEVS=()
verbose=0
exclude_dirs=(
    lost+found
)

exclude_files=()

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
    DEVFILE=$1;
    BLOCKSIZE=1k
    COUNT=256
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext2 $DEVFILE 0;
}

unset_ext2() {
    :
}

setup_ext4() {
    DEVFILE=$1;
    BLOCKSIZE=1k
    COUNT=256
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext4 $DEVFILE 0;
}

unset_ext4() {
    :
}

JFFS2_EMPTY_DIR=/tmp/_empty_dir_$RANDOM
JFFS2_IMAGE=/tmp/jffs2.img
JFFS2_SIZE=262144

setup_jffs2() {
    DEVICE=$1;
    runcmd mkdir -p $JFFS2_EMPTY_DIR;
    runcmd mkfs.jffs2 --pad=$JFFS2_SIZE --root $JFFS2_EMPTY_DIR -o $JFFS2_IMAGE;
    runcmd dd if=$JFFS2_IMAGE of=$DEVICE;
}

unset_jffs2() {
    runcmd rmdir $JFFS2_EMPTY_DIR;
    runcmd rm -f $JFFS2_IMAGE;
}

setup_mtd() {
    runcmd modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024);
    runcmd modprobe mtdblock;
}

setup_xfs() {
    DEVFILE="/dev/ram0";
    if ! [ -b $DEVFILE ]; then
        echo "$DEVFILE is not found or is not a block device" >&2;
        echo "Please use 'sudo modprobe brd rd_size=<n_kb>' to setup ramdisks" >&2;
        return 1;
    fi

    ramdisk_sz=$(runcmd blockdev --getsize64 $DEVFILE);
    if [ "$ramdisk_sz" -lt 16777216 ]; then
        echo "XFS's minimum file system size is 16MB." >&2;
        echo "Your ramdisk device ($DEVFILE)'s size is $ramdisk_sz" >&2;
        return 1;
    fi

    runcmd mkfs.xfs -f $DEVFILE >&2;
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

    login_user=$(who am i | cut -d ' ' -f 1)
    chown -R $login_user:$login_user .
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
        if [ -z "$mc_pid" ] && [ "$counter" -gt 0 ]; then
            return 0;
        fi
        if [ -n "$mc_pid" ]; then
            counter=$(expr $counter + 1);
            echo -n "$counter," >> $output;
            cat /proc/$mc_pid/stat | cut -d ' ' --output-delimiter=',' -f 1,2,3,24 >> $output;
        fi
        sleep 1;
    done
}

runcmd losetup -D

n_fs=${#FSLIST[@]};
for i in $(seq 0 $(($n_fs-1))); do

    # Run individual file system setup scripts defined above
    fs=${FSLIST[$i]};
    DEVICE=${DEVLIST[$i]};
    setup_$fs $DEVICE;

    # Mount
    if [ "$(mount | grep /mnt/test-$fs)" ]; then
        runcmd umount -f /mnt/test-$fs;
    fi
    if [ -d /mnt/test-$fs ]; then
        runcmd rm -rf /mnt/test-$fs;
    fi
    runcmd mkdir -p /mnt/test-$fs;

    echo "Mounting $DEVICE on /mnt/test-$fs";
    runcmd mount -t $fs -o sync,noatime $DEVICE /mnt/test-$fs

    # Remove FS-specific artifacts (e.g. lost+found folder in ext*)
    # This ensures all file systems being tested have identical initial states
    for dir in ${exclude_dirs[@]}; do
        rmdir /mnt/test-$fs/$dir;
    done
    for file in ${exclude_files[@]}; do
        rm -f /mnt/test-$fs/$file;
    done

done

# Run test program
runcmd make CFLAGS='-DABORT_ON_FAIL=0'
echo 'Running file system checker...';
echo 'Please check stdout in output.log, stderr in error.log';
monitor &
./pan 2>error.log > output.log

generic_cleanup;

