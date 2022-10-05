#!/bin/bash

# Standalong setup script without using swarm

FSLIST=()
DEVSIZE_KB=()
DEVLIST=()
SWARM_ID=0 # 0 is the default swarm id without using swarm
MCFSLIST=""
USE_ENV_VAR=0

LOOPDEVS=()
verbose=0
POSITIONAL=()
_CFLAGS=""
KEEP_FS=0
SETUP_ONLY=0
CLEAN_AFTER_EXP=0
REPLAY=0
exclude_dirs=(
    lost+found
)
JFFS2_IMAGE=/tmp/jffs2.img
VERIFS_PREFIX="veri"
VERI_PREFIX_LEN="${#VERIFS_PREFIX}"
PML_SRC="./demo.pml"
PML_TEMP="./.pml_tmp"
PML_START_PATN="\/\* The persistent content of the file systems \*\/"
PML_END_PATN="\/\* Abstract state signatures of the file systems \*\/"

exclude_files=()
# Create file system and device key-value map
declare -A FS_DEV_MAP
FS_DEV_MAP+=( ["btrfs"]="ram" ["ext2"]="ram" ["ext4"]="ram" ["f2fs"]="ram" )
FS_DEV_MAP+=( ["jffs2"]="mtdblock" ["ramfs"]="" ["tmpfs"]="" )
FS_DEV_MAP+=( ["verifs1"]="" ["verifs2"]="" ["xfs"]="ram" )
FS_DEV_MAP+=( ["ftfs"]="ram" )

FTFS_DEVFILE=$(losetup -f)
FTFS_PARTITION=/dev/sdc
FTFS_LOOP_FD=./dummy.dev
# BetrFS TODO: Set the ftfs ko path automatically
FTFS_KMOD=/home/yifei/betrfs/filesystem/ftfs.ko

mount_all() {
    SWARM_ID=$1;
    n_fs=${#FSLIST[@]};
    if [ $n_fs -eq 0 ]; then
        echo "Do not know which file systems and devices to mount"
        exit -1
    fi
    for i in $(seq 0 $(($n_fs-1))); do
        fs=${FSLIST[$i]};
        DEVICE=${DEVLIST[$i]};
        runcmd mount -t $fs $DEVICE /mnt/test-$fs-i$i-s$SWARM_ID;
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
        -c|--clean-after-exp)
            CLEAN_AFTER_EXP=1
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
            mount_all $SWARM_ID;
            exit 0;
            shift
            ;;
        -f|--fslist)
            MCFSLIST="$2"
            shift
            shift
            ;;
        -e|--use-env)
            USE_ENV_VAR=1
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

# Populate file system list and device size list
TOK_CNT="0"
IFS=':' read -ra ADDR <<< "$MCFSLIST"
for EACH_TOK in "${ADDR[@]}"; do
    if [ "$(($TOK_CNT % 2))" -eq 0 ]
    then
        FSLIST[$(($TOK_CNT / 2))]="$EACH_TOK"
    else
        DEVSIZE_KB[$(($TOK_CNT / 2))]="$EACH_TOK"
    fi
    TOK_CNT=$(($TOK_CNT + 1))
done

# Get the number of file systems
n_fs=${#FSLIST[@]};

# Get each device name in device list
ALL_RAMS=0
ALL_MTDBLOCKS=0
RAM_NAME="ram"
MTDBLOCK_NAME="mtdblock"

# Number of ram and mtdblocks to use
for i in $(seq 0 $(($n_fs-1))); do
    fs=${FSLIST[$i]};
    dev_type=${FS_DEV_MAP[${fs}]}
    if [ "$dev_type" = "$RAM_NAME" ]
    then
        ALL_RAMS=$(($ALL_RAMS + 1))
    elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
    then
        ALL_MTDBLOCKS=$(($ALL_MTDBLOCKS + 1))
    fi
done

# Populate DEVLIST
RAM_CNT=0
MTDBLOCK_CNT=0
for i in $(seq 0 $(($n_fs-1))); do
    fs=${FSLIST[$i]};
    dev_type=${FS_DEV_MAP[${fs}]}
    if [ "$dev_type" = "$RAM_NAME" ]
    then
        RAM_ID=$(($SWARM_ID * $ALL_RAMS + $RAM_CNT))
        RAM_CNT=$(($RAM_CNT + 1))
        DEVLIST[$i]="/dev/ram$RAM_ID"
    elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
    then
        MTDBLOCK_ID=$(($SWARM_ID * $ALL_MTDBLOCKS + $MTDBLOCK_CNT))
        MTDBLOCK_CNT=$(($MTDBLOCK_CNT + 1))
        DEVLIST[$i]="/dev/mtdblock$MTDBLOCK_ID"
    elif [ "$dev_type" = "" ]
    then
        DEVLIST[$i]=""
    else
        echo "[Error] cannot find proper dev type"
        exit -1;
    fi
done

generic_cleanup() {
    n_fs=$1;
    SWARM_ID=$2;
    if [ "$KEEP_FS" = "0" ]; then
        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            if [ "$(mount | grep /mnt/test-$fs-i$i-s$SWARM_ID)" ]; then
                umount -f /mnt/test-$fs-i$i-s$SWARM_ID;
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
        generic_cleanup $n_fs $SWARM_ID;
        exit $ret;
    fi
}

runcmd losetup -D

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
    DEVSIZEKB=$2;
    BLOCKSIZE=1k
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$DEVSIZEKB status=none;

    setup_ext ext2 $DEVFILE 0;
}

unset_ext2() {
    :
}

setup_ext4() {
    DEVFILE=$1;
    DEVSIZEKB=$2;
    BLOCKSIZE=1k
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$DEVSIZEKB status=none;

    setup_ext ext4 $DEVFILE 0;
}

unset_ext4() {
    :
}

setup_jffs2() {
    DEVICE=$1;
    DEVSIZE_KB=$2;
    JFFS2_SIZE=$(($DEVSIZE_KB * 1024))
    JFFS2_EMPTY_DIR=/tmp/_empty_dir_$RANDOM
    if ! [ "$(lsmod | grep mtdram)" ]; then
        setup_mtd $JFFS2_SIZE;
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
    JFFS2_SIZE=$1;
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

setup_ftfs() {
    DEVICE=$1
    DEVSIZEKB=$2
    BLOCKSIZE=1k
    runcmd dd if=/dev/zero of=$DEVICE bs=$BLOCKSIZE count=$DEVSIZE_KB status=none;

    runcmd ./mkfs.ftfs $FTFS_PARTITION
    runcmd insmod $FTFS_KMOD sb_dev=$FTFS_PARTITION sb_fstype=ext4
}

unset_ftfs() {
    rmmod ftfs
    losetup -D
}

# Setup mount points and each file system
for i in $(seq 0 $(($n_fs-1))); do
    # Run individual file system setup scripts defined above
    fs=${FSLIST[$i]};
    DEVICE=${DEVLIST[$i]};
    DEVSZKB=${DEVSIZE_KB[$i]};
    # Do not need to set up VeriFS
    if [ "${fs:0:${VERI_PREFIX_LEN}}" != "$VERIFS_PREFIX" ]; then
        # Unmount first
        if [ "$(mount | grep /mnt/test-$fs-i$i-s$SWARM_ID)" ]; then
            runcmd umount -f /mnt/test-$fs-i$i-s$SWARM_ID;
        fi

        setup_$fs $DEVICE $DEVSZKB;

        if [ -d /mnt/test-$fs-i$i-s$SWARM_ID ]; then
            runcmd rm -rf /mnt/test-$fs-i$i-s$SWARM_ID;
        fi
        runcmd mkdir -p /mnt/test-$fs-i$i-s$SWARM_ID;
    fi
done

# Insert c_track statements in promela code
C_TRACK_CNT=0
CTRACKLIST=()
for i in $(seq 0 $(($n_fs-1))); do
    DEVICE=${DEVLIST[$i]};
    DEVSZKB=${DEVSIZE_KB[$i]};
    if [ "$DEVICE" != "" ]; then
        CTRACKLIST[$i]="c_track \"get_fsimgs()[$C_TRACK_CNT]\" \"$(($DEVSZKB * 1024))\" \"UnMatched\";"
        C_TRACK_CNT=$(($C_TRACK_CNT+1))
    fi
done

C_TRACK_STMT=""
for i in $(seq 0 $(($C_TRACK_CNT-1))); do
    C_TRACK_STMT="${C_TRACK_STMT}${CTRACKLIST[$i]}\\n"
done

sed "/$PML_START_PATN/,/$PML_END_PATN/{//!d}" $PML_SRC > $PML_TEMP
sed "/$PML_START_PATN/a$C_TRACK_STMT" $PML_TEMP > $PML_SRC

# Run test program
if [ "$SETUP_ONLY" != "1" ]; then
    runcmd make CFLAGS=$_CFLAGS;
    echo 'Running file system checker...';
    echo 'Please check stdout in output.log, stderr in error.log';
    # Set environment variable MCFS_FSLIST for MCFS C Sources
    if [ "$USE_ENV_VAR" = "1" ]; then
        export MCFS_FSLIST$SWARM_ID="$MCFSLIST"
        ./pan -K $SWARM_ID 2>error.log > output.log
    else
        ./pan -K $SWARM_ID:$MCFSLIST 2>error.log > output.log
    fi

    # By default we don't want to clean up the file system for
    # better analyzing discrepancies reported by MCFS
    generic_cleanup $n_fs $SWARM_ID;
fi

# Run replayer
if [ "$REPLAY" = "1" ]; then
    runcmd make replayer
    echo 'Running the replayer...';
    echo 'The output is in replay.log';
    ./replay 2>&1 > replay.log
    mount_all $SWARM_ID;
fi
