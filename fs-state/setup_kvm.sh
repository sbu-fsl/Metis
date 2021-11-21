#!/bin/bash

FSLIST=(ext4 ext2)
DEVLIST=(/dev/ram0 /dev/ram0)
KVMLIST=(core-current-zero core-current-one)
KVM_IP=("192.168.122.225" "192.168.122.186")
# Ideally, two VMs have the same user
USER=root
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
    # Fourth arg is the path of the vm
    ip=$4

    if [ "$require_losetup" = "1" ]; then
        # Set up loop device if required
        DEVICE=$(runcmd_kvm $ip losetup --show -f $IMGFILE);
        echo "Setup loop device $LOOPDEV to forward $IMGFILE." >&2;
        LOOPDEVS+=("$DEVICE");
    else
        # Otherwise regard f/s image as the device
        DEVICE=$IMGFILE;
    fi

    # Format device
    runcmd_kvm $ip "mkfs.$fstype $DEVICE" >&2;

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
    IP=$4

    __runcmd_kvm $IP "test -b $DEVFILE"
    block_dev_exists=$?
    if [ "$block_dev_exists" -ne "0" ]; then
        echo "$DEVFILE is not found or is not a block device" >&2;
        return 1;
    fi

    # TODO: blockdev does not exist in KVM
    ramdisk_sz=$(runcmd_kvm $IP blockdev --getsize64 $DEVFILE);
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
    IP=$2;
    BLOCKSIZE=1k
    COUNT=256
    runcmd_kvm $IP dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext2 $DEVFILE 0 $IP;
}

unset_ext2() {
    :
}

setup_ext4() {
    DEVFILE=$1;
    IP=$2;
    BLOCKSIZE=1k
    COUNT=256
    runcmd_kvm $IP dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none;

    setup_ext ext4 $DEVFILE 0 $IP;
}

unset_ext4() {
    :
}

generic_cleanup() {
    if [ "$KEEP_FS" = "0" ]; then
        n_fs=${#FSLIST[@]};
        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            IP=${KVM_IP[$i]};
            __runcmd_kvm $IP "mount | grep /mnt/test-$fs"
            is_fs_mounted=$?
            if [ "$is_fs_mounted" -eq "0" ]; then
                __runcmd_kvm $IP "umount -f /mnt/test-$fs";
            fi
        done

        n_loop=${#LOOPDEVS[@]};
        for i in $(seq 0 $(($n_loop-1))); do
            device=${LOOPDEVS[$i]};
            IP=${KVM_IP[$i]};
            if [ "$device" ]; then
                __runcmd_kvm $IP losetup -d $device;
            fi
        done

        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            IP=${KVM_IP[$i]};

            unset_$fs $IP;
        done
    fi

    login_user=$(who am i | cut -d ' ' -f 1)
    chown -R $login_user:$login_user .
}

__runcmd_kvm() {
    ip="$1"; shift
    cmd=\"$@\"
    runcmd="ssh $USER@$ip $cmd"
    if [ $verbose != "0" ]; then
        echo "On the KVM $ip >>> $cmd" >&2 ;
    fi

    sleep 0.5;
    eval $runcmd;

    return $?
}

runcmd_kvm() {
    __runcmd_kvm "$@"
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
        IP=${KVM_IP[$i]};
        runcmd_kvm $IP mount -t $fs $DEVICE /mnt/test-$fs;
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

# TODO: losetup -D does not exist in kvm
# runcmd_kvm losetup -D

if [ "$SKIP_SETUP" != "1" ]; then

    n_fs=${#FSLIST[@]};
    for i in $(seq 0 $(($n_fs-1))); do

        # Run individual file system setup scripts defined above
        fs=${FSLIST[$i]};
        DEVICE=${DEVLIST[$i]};
        IP=${KVM_IP[$i]};

        # Unmount first
        __runcmd_kvm $IP "mount |grep /mnt/test-$fs"
        is_fs_mounted=$?
        if [ "$is_fs_mounted" -eq "0" ]; then
            runcmd_kvm $IP umount -f /mnt/test-$fs;
        fi

        setup_$fs $DEVICE $IP;

        __runcmd_kvm $IP "test -d /mnt/test-$fs"
        mount_dir_exists=$?
        if [ "$mount_dir_exists" -eq "0" ]; then
            runcmd_kvm $IP rm -rf /mnt/test-$fs;
        fi
        runcmd_kvm $IP mkdir -p /mnt/test-$fs;

    done
fi

# Run test program
if [ "$SETUP_ONLY" != "1" ]; then
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
