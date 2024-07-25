#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# This script intends to run Metis experiments for checking multiple 
# file systems (greater than 2) concurrently, including checking a 
# same file system multiple times.

# Usage: ./multi_fs.sh <fs1>:<size1>:<fs2>:<size2>:...:<fsN>:<sizeN>
MCFSLIST=""
FSLIST=()
DEVSIZE_KB=()
DEVLIST=()

# Create file system and device key-value map, copied from setup.sh
declare -A FS_DEV_MAP
FS_DEV_MAP+=( ["btrfs"]="ram" ["ext2"]="ram" ["ext4"]="ram" ["f2fs"]="ram" )
FS_DEV_MAP+=( ["jffs2"]="mtdblock" ["ramfs"]="" ["tmpfs"]="" )
FS_DEV_MAP+=( ["verifs1"]="" ["verifs2"]="" ["xfs"]="ram" ["nilfs2"]="ram" ["jfs"]="ram")
FS_DEV_MAP+=( ["nova"]="pmem" ["nfs-ganesha-ext4"]="ram" ["nfs-ganesha-verifs2"]="" )
FS_DEV_MAP+=( ["nfs-ext4"]="ram" ["nfs-verifs2"]="" )

# Pass the list of file systems and sizes to "MCFSLIST" 
MCFSLIST=$1

# Populate file system list and device size list, copied from setup.sh
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
RAM_NAME="ram"
MTDBLOCK_NAME="mtdblock"
PMEM_NAME="pmem"
# Populate the device list to determine the device type, copied from setup.sh
# Remove all uses of SWARM_ID, ALL_RAMS, ALL_MTDBLOCKS, ALL_PMEMS, RAM_ID, MTDBLOCK_ID, PMEM_ID
IS_RAM_UNIFORM=1 # 1 means all ramdisks are the same size, 0 means not
RD_SIZES="" # Use it only if not all the ramdisks have the same size (IS_RAM_UNIFORM=0)
LAST_RD_SIZE=0
FIRST_RD=1 # whether we are now processing the first ramdisk
# Count of different types of devices
RAM_CNT=0
MTDBLOCK_CNT=0
PMEM_CNT=0

for i in $(seq 0 $(($n_fs-1))); do
    fs=${FSLIST[$i]};
    dev_type=${FS_DEV_MAP[${fs}]}
    if [ "$dev_type" = "$RAM_NAME" ]
    then
        if [ "$FIRST_RD" -eq 1 ]; then
            LAST_RD_SIZE=${DEVSIZE_KB[$i]}
            RD_SIZES="$RD_SIZES${DEVSIZE_KB[$i]}"
            FIRST_RD=0
        else
            RD_SIZES="$RD_SIZES,${DEVSIZE_KB[$i]}"
            if [ "$LAST_RD_SIZE" -ne ${DEVSIZE_KB[$i]} ]; then
                IS_RAM_UNIFORM=0
            fi
        fi
        DEVLIST[$i]="/dev/ram$RAM_CNT"
        RAM_CNT=$(($RAM_CNT + 1))
    elif [ "$dev_type" = "$MTDBLOCK_NAME" ]
    then
        DEVLIST[$i]="/dev/mtdblock$MTDBLOCK_CNT"
        MTDBLOCK_CNT=$(($MTDBLOCK_CNT + 1))
    elif [ "$dev_type" = "$PMEM_NAME" ]
    then
        DEVLIST[$i]="/dev/pmem$PMEM_CNT"
        PMEM_CNT=$(($PMEM_CNT + 1))
    elif [ "$dev_type" = "" ]
    then
        DEVLIST[$i]=""
    else
        echo "[Error] cannot find proper dev type"
        exit -1;
    fi
done

# TODO: Setup ramdisk and mtdblock devices only, omit pmem devices due 
# to it requires an additional configuration step
cd ..
sudo ./stop.sh
# For ramdisks:
# Check if we use vanilla brd module or our own brd2 module
if [ "$RAM_CNT" -gt 0 ]; then
    # All the ramdisks have the same size
    if [ "$IS_RAM_UNIFORM" -eq 1 ]; then 
        modprobe brd rd_nr=$RAM_CNT rd_size=${DEVSIZE_KB[0]}
    else
        cd ../kernel/brd-for-$(uname -r)/
        sudo rmmod brd
        make -C /lib/modules/$(uname -r)/build M=$(pwd)
        sudo insmod brd.ko rd_nr=$RAM_CNT rd_sizes=$RD_SIZES
        cd ../../fs-state/
    fi
fi

# for mtdblock devices:
if [ "$MTDBLOCK_CNT" -gt 0 ]; then
    modprobe mtdram total_size=256 erase_size=16
    modprobe mtdblock
fi

# Run Metis with the given file systems and sizes
sudo ./setup.sh -f $MCFSLIST
