#!/bin/bash

FSLIST=()
DEVSIZE_KB=()
DEVLIST=()
SWARM_ID=0
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
VERIFS_PREFIX="veri"
VERI_PREFIX_LEN="${#VERIFS_PREFIX}"

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
    JFFS2_IMAGE=/tmp/jffs2.img
    if ! [ "$(lsmod | grep mtdram)" ]; then
        setup_mtd $JFFS2_SIZE;
    fi
    runcmd mkdir -p $JFFS2_EMPTY_DIR;
    runcmd mkfs.jffs2 --pad=$JFFS2_SIZE --root=$JFFS2_EMPTY_DIR -o $JFFS2_IMAGE;
    runcmd dd if=$JFFS2_IMAGE of=$DEVICE;
}

unset_jffs2() {
    JFFS2_IMAGE=/tmp/jffs2.img
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

generic_cleanup() {
    n_fs=$1;
    SWARM_ID=$2;
    if [ "$KEEP_FS" = "0" ]; then
        for i in $(seq 0 $(($n_fs-1))); do
            fs=${FSLIST[$i]};
            if [ "$(mount | grep /mnt/test-$fs-$i-$SWARM_ID)" ]; then
                umount -f /mnt/test-$fs-$i-$SWARM_ID;
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

mount_all() {
    SWARM_ID=$1;
    n_fs=${#FSLIST[@]};
    for i in $(seq 0 $(($n_fs-1))); do
        fs=${FSLIST[$i]};
        DEVICE=${DEVLIST[$i]};
        runcmd mount -t $fs $DEVICE /mnt/test-$fs-$i-$SWARM_ID;
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
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

# Create file system and device key-value map
declare -A FS_DEV_MAP
FS_DEV_MAP+=( ["btrfs"]="ram" ["ext2"]="ram" ["ext4"]="ram" ["f2fs"]="ram" )
FS_DEV_MAP+=( ["jffs2"]="mtdblock" ["ramfs"]="" ["tmpfs"]="" )
FS_DEV_MAP+=( ["verifs1"]="" ["verifs2"]="" ["xfs"]="ram" )

FIRST_TOK=true
TOK_CNT="-1"
# Populate FSLIST and DEVSIZE_KB
IFS=':' read -ra ADDR <<< "$MCFSLIST"
for EACH_TOK in "${ADDR[@]}"; do
    if [ "$FIRST_TOK" = true ] 
    then
        SWARM_ID=$EACH_TOK
        FIRST_TOK=false
    elif [ "$(($TOK_CNT % 2))" -eq 0 ]
    then 
        FSLIST[$(($TOK_CNT / 2))]="$EACH_TOK"
    else
        DEVSIZE_KB[$(($TOK_CNT / 2))]="$EACH_TOK"
    fi
    TOK_CNT=`expr $TOK_CNT + 1`
done

n_fs=${#FSLIST[@]};

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
        ALL_RAMS=`expr $ALL_RAMS + 1`
    elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
    then 
        ALL_MTDBLOCKS=`expr $ALL_MTDBLOCKS + 1`
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
        RAM_CNT=`expr $RAM_CNT + 1`
        DEVLIST[$i]="/dev/ram$RAM_ID"
    elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
    then
        MTDBLOCK_ID=$(($SWARM_ID * $ALL_MTDBLOCKS + $MTDBLOCK_CNT))
        MTDBLOCK_CNT=`expr $MTDBLOCK_CNT + 1`
        DEVLIST[$i]="/dev/mtdblock$MTDBLOCK_ID"
    elif [ "$dev_type" = "" ]
    then
        DEVLIST[$i]=""
    else
        echo "[Error] cannot find proper dev type"
        exit -1;
    fi
done

for i in $(seq 0 $(($n_fs-1))); do

    # Run individual file system setup scripts defined above
    fs=${FSLIST[$i]};
    DEVICE=${DEVLIST[$i]};
    DEVSZKB=${DEVSIZE_KB[$i]};

    if [ "${fs:0:${VERI_PREFIX_LEN}}" != "$VERIFS_PREFIX" ]; then
        # Unmount first
        if [ "$(mount | grep /mnt/test-$fs-$i-$SWARM_ID)" ]; then
            runcmd umount -f /mnt/test-$fs-$i-$SWARM_ID;
        fi

        setup_$fs $DEVICE $DEVSZKB;

        if [ -d /mnt/test-$fs-$i-$SWARM_ID ]; then
            runcmd rm -rf /mnt/test-$fs-$i-$SWARM_ID;
        fi
        runcmd mkdir -p /mnt/test-$fs-$i-$SWARM_ID;
    fi
done

PML_SRC="./demo.pml"
LINE_NUM=10
C_TRACK_CNT=0

for i in $(seq 0 $(($n_fs-1))); do
    DEVICE=${DEVLIST[$i]};
    DEVSZKB=${DEVSIZE_KB[$i]};
    if [ "$DEVICE" != "" ]; then
        sed -i "$LINE_NUM i c_track \"get_fsimgs()[$C_TRACK_CNT]\" \"$(($DEVSZKB * 1024))\" \"UnMatched\";" $PML_SRC
        LINE_NUM=$(($LINE_NUM+1))
        C_TRACK_CNT=$(($C_TRACK_CNT+1))
    fi
done


export MCFS_FSLIST="$MCFSLIST"

# Run test program
if [ "$SETUP_ONLY" != "1" ]; then
    runcmd make "CFLAGS=$_CFLAGS";
    echo 'Running file system checker...';
    echo 'Please check stdout in output.log, stderr in error.log';
    ./pan 2>error.log > output.log

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

