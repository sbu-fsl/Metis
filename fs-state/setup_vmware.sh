#!/bin/bash

FSLIST=(ext4 ext2)
DEVLIST=(/dev/ram0 /dev/ram0)
VMLIST=(/mnt/vms/vmware/tcl11_vmware1/tcl11_vmware1.vmx /mnt/vms/vmware/tcl11_vmware2/tcl11_vmware2.vmx)
LOOPDEVS=()
verbose=0
POSITIONAL=()
_CFLAGS=""
KEEP_FS=0
SETUP_ONLY=0
SKIP_SETUP=0
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
    # Fourth arg is the path of the vm
    vm=$4

    if [ "$require_losetup" = "1" ]; then
        # Set up loop device if required
        DEVICE=$(runcmd_vmware $vm losetup --show -f $IMGFILE);
        echo "Setup loop device $LOOPDEV to forward $IMGFILE." >&2;
        LOOPDEVS+=("$DEVICE");
    else
        # Otherwise regard f/s image as the device
        DEVICE=$IMGFILE;
    fi

    # Format device
    runcmd_vmware $vm "mkfs.$fstype $DEVICE" >&2;

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
    VM=$4

    __runcmd_vmware $VM "test -b $DEVFILE"
    block_dev_exists=$?
    if [ "$block_dev_exists" -ne "0" ]; then
        echo "$DEVFILE is not found or is not a block device" >&2;
        return 1;
    fi

    # TODO: blockdev does not exist in VM
    ramdisk_sz=$(runcmd_vmware $VM blockdev --getsize64 $DEVFILE);
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
    VM=$2;
    BLOCKSIZE=1k
    COUNT=256
    runcmd_vmware $VM dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext2 $DEVFILE 0 $VM;
}

unset_ext2() {
    :
}

setup_ext4() {
    DEVFILE=$1;
    VM=$2;
    BLOCKSIZE=1k
    COUNT=256
    runcmd_vmware $VM dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext4 $DEVFILE 0 $VM;
}

unset_ext4() {
    :
}

JFFS2_EMPTY_DIR=/tmp/_empty_dir_$RANDOM
JFFS2_IMAGE=/tmp/jffs2.img
JFFS2_SIZE=262144

setup_jffs2() {
    DEVICE=$1;
    VM=$2;
    if ! [ "$(lsmod | grep mtdram)" ]; then
        setup_mtd $VM;
    fi
    runcmd_vmware $VM mkdir -p $JFFS2_EMPTY_DIR;
    runcmd_vmware $VM mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_EMPTY_DIR -o $JFFS2_IMAGE;
    runcmd_vmware $VM dd if=$JFFS2_IMAGE of=$DEVICE;
}

unset_jffs2() {
    VM=$1;
    runcmd_vmware $VM rmdir /tmp/_empty_dir*;
    runcmd_vmware $VM rm -f $JFFS2_IMAGE;
}

setup_f2fs() {
    DEVFILE=$1;
    VM=$2;

    devsize=$(runcmd_host verify_device $DEVFILE f2fs $(expr 40 \* 1024 \* 1024) $VM)
    runcmd_vmware $VM dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd_vmware $VM mkfs.f2fs -f $DEVFILE >&2;
}

unset_f2fs() {
    :
}

setup_btrfs() {
    DEVFILE=$1;
    VM=$2;

    devsize=$(runcmd_host verify_device $DEVFILE btrfs 114294784 $VM);
    runcmd_vmware $VM dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd_vmware $VM mkfs.btrfs -f $DEVFILE >&2;
}

unset_btrfs() {
    :
}

setup_mtd() {
    VM=$1
    runcmd_vmware $VM modprobe mtdram total_size=$(expr $JFFS2_SIZE / 1024) erase_size=16;
    runcmd_vmware $VM modprobe mtdblock;
}

setup_xfs() {
    DEVFILE="$1";
    VM=$2;

    devsize=$(runcmd_host verify_device $DEVFILE xfs $(expr 16 \* 1024 \* 1024) $VM)
    runcmd_vmware $VM dd if=/dev/zero of=$DEVFILE bs=1k count=$(expr $devsize / 1024)
    runcmd_vmware $VM mkfs.xfs -f $DEVFILE >&2;
}

unset_xfs() {
    :
}

generic_cleanup() {
    if [ "$KEEP_FS" = "0" ]; then
        n_fs=${#FSLIST[@]};
        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            VM=${VMLIST[$i]};
     
            __runcmd_vmware $VM "mount |grep /mnt/test-$fs"
	    is_fs_mounted=$?
            if [ "$is_fs_mounted" -eq "0" ]; then
                __runcmd_vmware $VM "sudo umount -f /mnt/test-$fs";
            fi
        done

        # TODO: Not passing the vm for loop devices. Figure out correct way later
        for device in ${LOOPDEVS[@]}; do
            __runcmd_vmware "test $device"
	    dev_exists=$?
            if [ "$dev_exists" -eq "0" ]; then
                __runcmd_vmware "losetup -d $device";
            fi
        done

        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            VM=${VMLIST[$i]};
     
            unset_$fs $VM;
        done
    fi

    login_user=$(who am i | cut -d ' ' -f 1)
    chown -R $login_user:$login_user .
}

__runcmd_vmware() {
    vm="$1"; shift
    cmd=\"$@\"
    runcmd="sudo vmrun -T ws -gu tc -gp Pa55word runScriptInGuest $vm /bin/sh $cmd"
    if [ $verbose != "0" ]; then
        echo "On VM $vm >>> $cmd" >&2 ;
    fi

    sleep 0.5;
    eval $runcmd;
    
    return $?
}

runcmd_vmware() {
    __runcmd_vmware "$@"
    ret=$?
    if [ "$ret" -ne "0" ]; then
        echo "Command '$0' exited with error ($ret)." >&2;
        generic_cleanup;
        exit $ret;
    fi
}

runcmd_host() {
    if [ $verbose != "0" ]; then
        echo "On Host >>> $@" >&2 ;
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
        VM=${VMLIST[$i]};
        runcmd_vmware $VM sudo mount -t $fs $DEVICE /mnt/test-$fs;
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
        -p|--skip)
            SKIP_SETUP=1
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

# TODO: losetup -D does not exist in vm
# runcmd_vmware losetup -D

if [ "$SKIP_SETUP" != "1" ]; then

    n_fs=${#FSLIST[@]};
    for i in $(seq 0 $(($n_fs-1))); do

        # Run individual file system setup scripts defined above
        fs=${FSLIST[$i]};
        DEVICE=${DEVLIST[$i]};
        VM=${VMLIST[$i]};

        # Unmount first
        __runcmd_vmware $VM "mount |grep /mnt/test-$fs"
        is_fs_mounted=$?
        if [ "$is_fs_mounted" -eq "0" ]; then
            runcmd_vmware $VM sudo umount -f /mnt/test-$fs;
        fi

        setup_$fs $DEVICE $VM;

        __runcmd_vmware $VM "test -b $DEVICE"
        block_dev_exists=$?
        if [ "$block_dev_exists" -eq "0" ]; then
            runcmd_vmware $VM rm -rf /mnt/test-$fs;
        fi
        runcmd_vmware $VM mkdir -p /mnt/test-$fs;

    done
fi

# Run test program
if [ "$SETUP_ONLY" != "1" ]; then
    export DISPLAY=:1.0
    runcmd_host make "CFLAGS=$_CFLAGS";
    echo 'Running file system checker...';
    echo 'Please check stdout in output.log, stderr in error.log';
    ./pan 2>error.log > output.log

    generic_cleanup;
fi

# Run replayer
if [ "$REPLAY" = "1" ]; then
    runcmd_host make replayer
    echo 'Running the replayer...';
    echo 'The output is in replay.log';
    ./replay 2>&1 > replay.log
    mount_all;
fi

