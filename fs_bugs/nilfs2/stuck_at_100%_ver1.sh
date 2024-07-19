#!/bin/bash -x

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
  for i in $(seq 1 $NUM_FILES_TO_CREATE); do
    FILE="${FILE_PREFIX}_${i}"
    sudo dd if=/dev/zero of="${MOUNT_POINT}/${FILE}" bs=1K count=${FILE_SIZE} status=none
    if [ $? -ne 0 ]; then
        echo "Failed to create file ${MOUNT_POINT}/${FILE}. Stopping."
        break
    fi
    echo -e "\nCreated ${MOUNT_POINT}/${FILE}"

    # df "${MOUNT_POINT}"
    # df -h "${MOUNT_POINT}"
    # df -i "${MOUNT_POINT}"
    # sudo lssu -a -l /dev/ram1
done

}

delete_files() {
    local num_directories=$(find ${MOUNT_POINT} -maxdepth 1 -type f | wc -l)
    for i in $(seq 1 "$num_directories"); do
        FILE="${MOUNT_POINT}/${FILE_PREFIX}_${i}"
        sudo rm -f "$FILE"
        echo "Deleted ${FILE}"
        # if [ "$SLEEP" -ne 0 ]; then
        #     sleep $SLEEP            
        # fi
        # df "${MOUNT_POINT}"
        # df -h "${MOUNT_POINT}"
        # df -i "${MOUNT_POINT}"
        # sudo lssu -a -l /dev/ram1
    done
}

create_and_delete() {
    echo -e "\n\nCreating files until the system is full."
    create_files

    sleep 15

    echo -e "\n\nDisk usage after filling:"
    df "${MOUNT_POINT}"
    df -h "${MOUNT_POINT}"
    df -i "${MOUNT_POINT}"
    sudo lssu -a -l /dev/ram1

    echo -e "\n\nDeleting all files created"
    delete_files

    echo -e "\nDisk usage after deleting:"
    for i in $(seq 0 5); do
        echo "Checking usage at: $(date), i=$i" 
        df "${MOUNT_POINT}"
        df -h "${MOUNT_POINT}"
        df -i "${MOUNT_POINT}"
        sudo lssu -a -l /dev/ram1
        
        sleep 10
    done
}

## Initial setup 

# Update protection_period
if sudo grep -q "^${SETTING}[[:space:]]*" "$CONFIG_FILE"; then
    sudo sed -i "s|^\(${SETTING}[[:space:]]*\).*|\1${PROTECTION_PERIOD}|" "$CONFIG_FILE"
else
    echo "Did not find the setting ${SETTING}"
fi

sudo umount /mnt/test-nilfs2-i1-s0
sudo rm -rf /mnt/test-nilfs2-i1-s0
sudo mkdir /mnt/test-nilfs2-i1-s0
sudo rmmod brd
cd ~/Metis/kernel/brd-for-6.9.2/
make -C /lib/modules/$(uname -r)/build M=$(pwd)

sudo insmod brd.ko rd_nr=2 rd_sizes=256,1028
sudo mkfs.nilfs2 -B 16 -f /dev/ram1
sudo mount /dev/ram1 /mnt/test-nilfs2-i1-s0


## Disk usage after initialization
echo -e "\nInitial disk usage:"
df "${MOUNT_POINT}"
df -h "${MOUNT_POINT}"
df -i "${MOUNT_POINT}"
sudo lssu -a -l /dev/ram1
cat /etc/nilfs_cleanerd.conf

## Create files from an empty disk
create_and_delete

## Create files from a partially full disk
create_and_delete

create_and_delete

## Manually run cleanerd
nilfs_cleanerd -p 1 /dev/ram1 "${MOUNT_POINT}"
for i in $(seq 0 5); do
        echo "Checking usage at: $(date), i=$i" 
        df "${MOUNT_POINT}"
        df -h "${MOUNT_POINT}"
        df -i "${MOUNT_POINT}"
        sudo lssu -a -l /dev/ram1
        
        sleep 10
    done

