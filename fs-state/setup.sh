#!/bin/bash

#FSLIST=(ext4 jffs2)
FSLIST=(verifs2 zfs)
DEVLIST=(/dev/ram0 /dev/ram1)
LOOPDEVS=()
verbose=0
POSITIONAL=()
_CFLAGS=""
KEEP_FS=0
SETUP_ONLY=0
REPLAY=0
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

# Check if the given file is a block device and meets the size requirement
# If it's OK, the function will return the size of the device in bytes.
# Usage: verify_device <path> <fstype> <minimum_size_bytes>
verify_device() {
    DEVFILE=$1
    FSTYPE=$2
    MINSZ=$3

    if ! [ -b "$DEVFILE" ]; then
        echo "$DEVFILE is not found or is not a block device" >&2;
        return 1;
    fi

    ramdisk_sz=$(runcmd blockdev --getsize64 $DEVFILE);
    if [ "$ramdisk_sz" -lt "$MINSZ" ]; then
        echo "$FSTYPE's minimum file system size is $MINSZ bytes." >&2;
        echo "Your ramdisk device ($DEVFILE)'s size is $ramdisk_sz bytes." >&2;
        return 1;
    fi

    echo $ramdisk_sz;
    return 0;
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
    if ! [ "$(lsmod | grep mtdram)" ]; then
        setup_mtd;
    fi
    runcmd mkdir -p $JFFS2_EMPTY_DIR;
    runcmd mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_EMPTY_DIR -o $JFFS2_IMAGE;
    runcmd dd if=$JFFS2_IMAGE of=$DEVICE;
}

unset_jffs2() {
    runcmd rmdir /tmp/_empty_dir*;
    runcmd rm -f $JFFS2_IMAGE;
}

setup_f2fs() {
    DEVFILE=$1;

    devsize=$(runcmd verify_device $DEVFILE f2fs $(expr 40 \* 1024 \* 1024))
    runcmd dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd mkfs.f2fs -f $DEVFILE >&2;
}

unset_f2fs() {
    :
}

setup_btrfs() {
    DEVFILE=$1;

    devsize=$(runcmd verify_device $DEVFILE btrfs 114294784);
    runcmd dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd mkfs.btrfs -f $DEVFILE >&2;
}

unset_btrfs() {
    :
}

setup_mtd() {
    runcmd modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024) erase_size=16;
    runcmd modprobe mtdblock;
}

setup_xfs() {
    DEVFILE="$1";

    devsize=$(runcmd verify_device $DEVFILE xfs $(expr 16 \* 1024 \* 1024))
    runcmd dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd mkfs.xfs -f $DEVFILE >&2;
}

unset_xfs() {
    :
}

setup_zfs() { 
    #runcmd zfs create -o mountpoint=/mnt/test-zfs zpooltest/fs2
    echo "setup zfs begin"
    DEVFILE="$1";
    BLOCKSIZE=1k
    COUNT=256
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;
    #runcmd zpool create mcfszpool $DEVFILE
    runcmd zpool create mcfszpool $DEVFILE
    runcmd zfs set mountpoint=legacy mcfszpool
    runcmd zfs create mcfszpool/fs1
    mount -t zfs mcfszpool/fs1 /mnt/test-zfs
    #mount -t zfs mcfszpool/fs1 /mnt/test-zfs-ramblkdev
    #zfs create mcfszpool
    #zfs set mountpoint=legacy mcfszpool
    echo "setup zfs done"
}

unset_zfs() {
    #runcmd zfs destroy -r mcfszpool
    echo "here"
}


setup_verifs2() {
   cd ../../fuse-cpp-ramfs/src && make
   cd ../../fuse-cpp-ramfs/src && make install
   cd ../../fuse-cpp-ramfs/ && fuse-cpp-ramfs /mnt/test-verifs2 &
   cd ../../nfs4mc/fs-state
}

unset_verifs2() {
    echo "unset verifs2"
}

generic_cleanup() {
    if [ "$KEEP_FS" = "0" ]; then
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
    fi

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

mount_all() {
    n_fs=${#FSLIST[@]};
    for i in $(seq 0 $(($n_fs-1))); do
        fs=${FSLIST[$i]};
        DEVICE=${DEVLIST[$i]};
        if [ "$fs" == "zfs" ];then
            runcmd mount -t zfs mcfszpool/fs1 /mnt/test-zfs
        else
            runcmd mount -t $fs $DEVICE /mnt/test-$fs;
        fi
    done
}

# Parse command line options
while [[ $# -gt 0 ]]; do
    key=$1;
    case $key in
        -a|--abort-on-discrepancy)
            _CFLAGS="-DABORT_ON_FAIL=1";
            shift
            ;;
        -k|--keep-fs)
            KEEP_FS=1
            shift
            ;;
        -v|--verbose)
            verbose=1
            shift
            ;;
        -s|--setup-only)
            KEEP_FS=1
            SETUP_ONLY=1
            shift
            ;;
        -r|--replay)
            REPLAY=1
            SETUP_ONLY=1
            KEEP_FS=1
            shift
            ;;
        -m|--mount-all)
            mount_all;
            exit 0;
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

runcmd losetup -D

n_fs=${#FSLIST[@]};
for i in $(seq 0 $(($n_fs-1))); do

    # Run individual file system setup scripts defined above
    fs=${FSLIST[$i]};
    DEVICE=${DEVLIST[$i]};

    # Unmount first
    if [ "$(mount | grep /mnt/test-$fs)" ]; then
        runcmd umount -f /mnt/test-$fs;
    fi
    setup_$fs $DEVICE;

    #if [ -d /mnt/test-$fs ]; then
    #    runcmd rm -rf /mnt/test-$fs;
    #fi
    runcmd mkdir -p /mnt/test-$fs;

done

# Run test program
if [ "$SETUP_ONLY" != "1" ]; then
    runcmd make "CFLAGS=$_CFLAGS";
    echo 'Running file system checker...';
    echo 'Please check stdout in output.log, stderr in error.log';
    ./pan 2>error.log > output.log

    generic_cleanup;
fi

# Run replayer
if [ "$REPLAY" = "1" ]; then
    runcmd make replayer
    echo 'Running the replayer...';
    echo 'The output is in replay.log';
    ./replay 2>&1 > replay.log
    mount_all;
fi

