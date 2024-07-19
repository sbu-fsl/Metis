#!/bin/bash

if [ "$EUID" -ne 0 ]; then
  sudo "$0" "$@"
  exit $?
fi

# mode
SLEEP=0

# configurations
SETTING="protection_period"
PROTECTION_PERIOD="10"

# constants
CONFIG_FILE="/etc/nilfs_cleanerd.conf"
MOUNT_POINT="/mnt/test-nilfs2-i1-s0"
FILE_PREFIX="testfile"
DIR_PREFIX="testdir"
FILE_SIZE=4
NUM_FILES_TO_CREATE=100


update_setting() {
    local setting=$1
    local value=$2
    SETTING_MODIFIED=${setting}
    echo "setting: ${setting}, value: ${value}"
}


create_files() {
    local num_files=0
    for i in $(seq 1 $NUM_FILES_TO_CREATE); do
        FILE="${FILE_PREFIX}_${i}"
        dd if=/dev/zero of="${MOUNT_POINT}/${FILE}" bs=1K count=${FILE_SIZE} status=none
        if [ $? -ne 0 ]; then
            echo "Failed to create file ${MOUNT_POINT}/${FILE}. Stopping."
            break
        fi
        num_files=$((num_files + 1))
    done
    echo -e "\nCreated ${num_files} files"
}

delete_files() {
    local num_files=$(find ${MOUNT_POINT} -maxdepth 1 -type f | wc -l)
    for i in $(seq 1 "$num_files"); do
        FILE="${MOUNT_POINT}/${FILE_PREFIX}_${i}"
        rm -f "$FILE"
    done
    echo -e "\nDeleted ${num_files} files"
}

create_and_delete() {
    echo -e "\n\nCreating files until the system is full."
    create_files

    sleep 15

    echo -e "\n\nDisk usage after filling:"
    df "${MOUNT_POINT}"
    df -h "${MOUNT_POINT}"
    df -i "${MOUNT_POINT}"
    lssu -a -l /dev/ram1

    echo -e "\n\nDeleting all files created"
    delete_files

    sleep 60
        
    echo -e "\nDisk usage after deleting:"    
    df "${MOUNT_POINT}"
    df -h "${MOUNT_POINT}"
    df -i "${MOUNT_POINT}"
    lssu -a -l /dev/ram1
}

## Initial setup 

# Update protection_period
if grep -q "^${SETTING}[[:space:]]*" "$CONFIG_FILE"; then
    sed -i "s|^\(${SETTING}[[:space:]]*\).*|\1${PROTECTION_PERIOD}|" "$CONFIG_FILE"
else
    echo "Did not find the setting ${SETTING}"
fi

umount /mnt/test-nilfs2-i1-s0
rm -rf /mnt/test-nilfs2-i1-s0
mkdir /mnt/test-nilfs2-i1-s0
rmmod brd
cd /home/ubuntu/Metis/kernel/brd-for-6.9.2/
make -C /lib/modules/$(uname -r)/build M=$(pwd)

insmod brd.ko rd_nr=2 rd_sizes=256,1028
mkfs.nilfs2 -B 16 -f /dev/ram1
mount /dev/ram1 /mnt/test-nilfs2-i1-s0


## Disk usage after initialization
echo -e "\nInitial disk usage:"
df "${MOUNT_POINT}"
df -h "${MOUNT_POINT}"
df -i "${MOUNT_POINT}"
lssu -a -l /dev/ram1

## Create files from an empty disk
create_and_delete

## Create files from a partially full disk
create_and_delete

## Manually run cleanerd
nilfs_cleanerd -p 1 /dev/ram1 "${MOUNT_POINT}"

sleep 60
echo "Disk usage after manually running cleanerd" 
df "${MOUNT_POINT}"
df -h "${MOUNT_POINT}"
df -i "${MOUNT_POINT}"
lssu -a -l /dev/ram1


