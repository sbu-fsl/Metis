#!/bin/bash

FSLIST=()
DEVSIZE_KB=()
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
NUM_PAN=4 # default number of compilation options in swarm.lib
SWARM_CONF="swarm.lib"

exclude_files=()
# Create file system and device key-value map
declare -A FS_DEV_MAP
FS_DEV_MAP+=( ["btrfs"]="ram" ["ext2"]="ram" ["ext4"]="ram" ["f2fs"]="ram" )
FS_DEV_MAP+=( ["jffs2"]="mtdblock" ["ramfs"]="" ["tmpfs"]="" )
FS_DEV_MAP+=( ["verifs1"]="" ["verifs2"]="" ["xfs"]="ram" )

declare -A DEVLISTS

generic_cleanup() {
    n_fs=${#FSLIST[@]};
	for j in $(seq 1 $(($NUM_PAN))); do
		SWARM_ID=$j;
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

# Mount all file systems for a single swarm instance
mount_all() {
	n_fs=${#FSLIST[@]};
	if [ $n_fs -eq 0 ]; then
		echo "Do not know which file systems and devices to mount"
		exit -1
	fi
	for i in $(seq 1 $(($NUM_PAN))); do
		SWARM_ID=$i;
		for j in $(seq 0 $(($n_fs-1))); do
			fs=${FSLIST[$j]};
			DEVICE=${DEVLISTS[$i,$j]};
			runcmd mount -t $fs $DEVICE /mnt/test-$fs-i$j-s$SWARM_ID;
		done
	done
}

# Get NUM_PAN from swarm.lib
SWARM_NUM_LINE=20
line=$(sed "${SWARM_NUM_LINE}!d" $SWARM_CONF)
NUM_PAN=$(echo "$line" | cut -d $'\t' -f2)

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
            mount_all;
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
        -n|--numpan)
            NUM_PAN="$2"
            shift
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

# Check if MCFSLIST is empty
if [ -z "$MCFSLIST" ]
then
	echo "-f should not be empty. Usage ./setup_swarm.sh -f fs1:sz1:fs2:sz2"
	exit -1
fi

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

# Populate DEVLISTS DEVLISTS[i,j]: i: swarm_id j: dev index for i-th swarm id
RAM_CNT=0
MTDBLOCK_CNT=0
for i in $(seq 1 $(($NUM_PAN))); do
	SWARM_ID=$i
	RAM_CNT=0
	MTDBLOCK_CNT=0
	for j in $(seq 0 $(($n_fs-1))); do
		fs=${FSLIST[$j]};
		dev_type=${FS_DEV_MAP[${fs}]}
		if [ "$dev_type" = "$RAM_NAME" ]
		then
			RAM_ID=$((($SWARM_ID - 1) * $ALL_RAMS + $RAM_CNT))
			RAM_CNT=$(($RAM_CNT + 1))
			DEVLISTS[$i,$j]="/dev/ram$RAM_ID"
		elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
		then
			MTDBLOCK_ID=$((($SWARM_ID - 1) * $ALL_MTDBLOCKS + $MTDBLOCK_CNT))
			MTDBLOCK_CNT=$(($MTDBLOCK_CNT + 1))
			DEVLISTS[$i,$j]="/dev/mtdblock$MTDBLOCK_ID"
		elif [ "$dev_type" = "" ]
		then
			DEVLISTS[$i,$j]=""
		else
			echo "[Error] cannot find proper dev type"
			exit -1;
		fi
	done
done

runcmd losetup -D


# Insert c_track statements in promela code
C_TRACK_CNT=0
CTRACKLIST=()
for i in $(seq 0 $(($n_fs-1))); do
    DEVICE=${DEVLISTS[1,$i]};
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

runcmd make parameters

if [ "$USE_ENV_VAR" = "1" ]; then
    for (( i=1; i<=$NUM_PAN; i++ )); do
        export MCFS_FSLIST$i="$MCFSLIST"
    done
fi

# Compile MCFS library: libsmcfs.a
runcmd make install
# Use ssh and scp to set up swarm for remotes
count=0
for i in $(grep -Po '\t.*:\d+( |\t)' ${SWARM_CONF}); do
	if [ $count -ge 1 ]; then
		remote=$(echo $i | awk -F ':' '{print $1}');
		scp libsmcfs.a "$remote":libsmcfs.a;
		scp parameters.pml "$remote":parameters.pml;
		scp Makefile "$remote":Makefile;
		scp 'stop.sh' "$remote":'stop.sh'
		ssh "$remote" "sh ./nfs-validator/fs-state/loadmods.sh" &
		if [ "$USE_ENV_VAR" = "1" ]; then
			for (( j=1; j<=$NUM_PAN; j++ )); do
				ssh "$remote" "MCFS_FSLIST$j=$MCFSLIST"
			done
		fi
	fi
	count=$((count+1));
done

runcmd swarm $SWARM_CONF -K $MCFSLIST -f demo.pml

runcmd ./demo.pml.swarm
