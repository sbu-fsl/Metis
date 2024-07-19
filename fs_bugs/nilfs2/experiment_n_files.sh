#!/bin/bash -x

usage() {
    echo "Usage not correct!"
    exit 1
}

# mode
REMOUNT=0
SLEEP=0

# device
DEVICE_SIZE=1028
NUM_BLOCKS=16

# default configurations
PROTECTION_PERIOD=10
MIN_CLEAN_SEG="10%"
MAX_CLEAN_SEG="20%"
CLEAN_CHECK_INTVL=10
NSEGMENTS_PER_CLEAN=2
MC_NSEGMENTS_PER_CLEAN=4
CLEAN_INTVL=5
MC_CLEAN_INTVL=1
RETRY_INTERVAL=60
MIN_RECLAIM_BLOCKS="10%"
MC_MIN_RECLAIM_BLOCKS="1%"

# for modifying configuration
SETTING_MODIFIED=""
DEFAULT_VALUE=""

# constants
CONFIG_FILE="/etc/nilfs_cleanerd.conf"
MOUNT_POINT="/mnt/test-nilfs2-i1-s0"
FILE_PREFIX="testfile"
DIR_PREFIX="testdir"
FILE_SIZE=4
NUM_FILES_TO_CREATE=50

ARGS=$(getopt -o l:d:b:p:ms:f: --long min:,max:,check_intvl:,nseg:,mc_nseg:,cl_intvl:,mc_cl_intvl:,retry:,min_reclaim:,mc_min_reclaim: -n 'single_experiment.sh' -- "$@")

if [ $? -ne 0 ]; then
    usage
fi

eval set -- "$ARGS"

update_setting() {
    local setting=$1
    local value=$2
    SETTING_MODIFIED=${setting}
    echo "setting: ${setting}, value: ${value}"
    if sudo grep -q "^${setting}[[:space:]]*" "$CONFIG_FILE"; then
        sudo sed -i "s|^\(${setting}[[:space:]]*\).*|\1${value}|" "$CONFIG_FILE"
    else
        echo "Did not find the setting ${setting}"
    fi

}

while true; do
    case "$1" in
        -l) 
            LOGFILE="$2"
            shift 2
            ;;
        -d)
            DEVICE_SIZE="$2"
            shift 2
            ;;
        -b)
            NUM_BLOCKS="$2"
            shift 2
            ;;
        -p)
            update_setting "protection_period" "$2"
            DEFAULT_VALUE=${PROTECTION_PERIOD}
            shift 2
            ;;
        -m)
            REMOUNT=1
            shift
            ;;
        -s)
            SLEEP="$2"
            shift 2
            ;;
        -f)
            NUM_FILES_TO_CREATE="$2"
            shift 2
            ;;
        --min)
            update_setting "min_clean_segments" "$2"
            DEFAULT_VALUE=${MIN_CLEAN_SEG}
            # MIN_CLEAN_SEG="$2"
            shift 2
            ;;
        --max)
            update_setting "max_clean_segments" "$2"
            DEFAULT_VALUE=${MAX_CLEAN_SEG}
            # MAX_CLEAN_SEG="$2"
            shift 2
            ;;
        --check_intvl)
            update_setting "clean_check_interval" "$2"
            DEFAULT_VALUE=${CLEAN_CHECK_INTVL}
            # CLEAN_CHECK_INTVL="$2"
            shift 2
            ;;
        --nseg)
            update_setting "nsegments_per_clean" "$2"
            DEFAULT_VALUE=${NSEGMENTS_PER_CLEAN}
            # NSEGMENTS_PER_CLEAN="$2"
            shift 2
            ;;
        --mc_nseg)
            update_setting "mc_nsegments_per_clean" "$2"
            DEFAULT_VALUE=${MC_NSEGMENTS_PER_CLEAN}
            # MC_NSEGMENTS_PER_CLEAN="$2"
            shift 2
            ;;
        --cl_intvl)
            update_setting "cleaning_interval" "$2"
            DEFAULT_VALUE=${CLEAN_INTVL}
            # CLEAN_INTVL="$2"
            shift 2
            ;;
        --mc_cl_intvl)
            update_setting "mc_cleaning_interval" "$2"
            DEFAULT_VALUE=${MC_CLEAN_INTVL}
            # MC_CLEAN_INTVL="$2"
            shift 2
            ;;
        --retry)
            update_setting "retry_interval" "$2"
            DEFAULT_VALUE=${RETRY_INTERVAL}
            # RETRY_INTERVAL="$2"
            shift 2
            ;;
        --min_reclaim)
            update_setting "min_reclaimable_blocks" "$2"
            DEFAULT_VALUE=${MIN_RECLAIM_BLOCKS}
            # MIN_RECLAIM_BLOCKS="$2"
            shift 2
            ;;
        --mc_min_reclaim)
            update_setting "mc_min_reclaimable_blocks" "$2"
            DEFAULT_VALUE=${MC_MIN_RECLAIM_BLOCKS}
            # MC_MIN_RECLAIM_BLOCKS="$2"
            shift 2
            ;;
        --)
            shift
            break
            ;;
        *)
            usage
            ;;
    esac
done





get_free_space() {
  df --output=avail "$MOUNT_POINT" | tail -n 1
}

create_files() {

  for i in $(seq 1 $NUM_FILES_TO_CREATE); do
    # FREE_SPACE=$(get_free_space)
    # echo "Free space: ${FREE_SPACE}"
    
    FILE="${FILE_PREFIX}_${i}"
    # DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
    
    # sudo mkdir "$DIR"
    # if [ $? -ne 0 ]; then
    #     echo "Stopping. "
    #     break
    # fi
    # echo "Created ${DIR}"
    
    sudo dd if=/dev/zero of="${MOUNT_POINT}/${FILE}" bs=1K count=${FILE_SIZE} status=none
    if [ $? -ne 0 ]; then
        echo "Failed to create file ${MOUNT_POINT}/${FILE}. Stopping."
        break
    fi
    echo -e "\nCreated ${MOUNT_POINT}/${FILE}"
    if [ "$SLEEP" -ne 0 ]; then
        # echo "sleeping ${SLEEP}"
        sleep "$SLEEP"
    fi
    df "${MOUNT_POINT}"
    df -h "${MOUNT_POINT}"
    df -i "${MOUNT_POINT}"
    sudo lssu -a -l /dev/ram1
done

}

delete_files() {
    local num_directories=$(find ${MOUNT_POINT} -maxdepth 1 -type f | wc -l
)
    for i in $(seq 1 "$num_directories"); do
        FILE="${MOUNT_POINT}/${FILE_PREFIX}_${i}"
        sudo rm -f "$FILE"
        echo "Deleted ${FILE}"
        if [ "$SLEEP" -ne 0 ]; then
            echo "sleeping ${SLEEP}"
            sleep $SLEEP            
        fi
        df "${MOUNT_POINT}"
            df -h "${MOUNT_POINT}"
            df -i "${MOUNT_POINT}"
            sudo lssu -a -l /dev/ram1
        
    done

    

}

# initial setup
mount() {
    sudo umount /mnt/test-nilfs2-i1-s0
    sudo rm -rf /mnt/test-nilfs2-i1-s0
    sudo mkdir /mnt/test-nilfs2-i1-s0
    sudo rmmod brd
    cd ~/Metis/kernel/brd-for-6.9.2/
    make -C /lib/modules/$(uname -r)/build M=$(pwd)

    sudo insmod brd.ko rd_nr=2 rd_sizes=256,$DEVICE_SIZE
    sudo mkfs.nilfs2 -B $NUM_BLOCKS -f /dev/ram1
    sudo mount /dev/ram1 /mnt/test-nilfs2-i1-s0
}

if [ "$REMOUNT" -eq 1 ]; then 
    mount 
fi

# disk usage after creating system
echo -e "\nInitial disk usage:"

df "${MOUNT_POINT}"
df -h "${MOUNT_POINT}"
df -i "${MOUNT_POINT}"
sudo lssu -a -l /dev/ram1
cat /etc/nilfs_cleanerd.conf


# cleaning up
if [[ -n "$SETTING_MODIFIED" && -n "$DEFAULT_VALUE" ]]; then
    sudo sed -i "s|^\(${SETTING_MODIFIED}[[:space:]]*\).*|\1${DEFAULT_VALUE}|" "$CONFIG_FILE"

    # echo -e "\nChanged configurations to default\n"
fi



echo -e "\n\nCreating files and directories"
create_files

sleep 15
echo -e "\n\nDisk usage after filling:"
df "${MOUNT_POINT}"
df -h "${MOUNT_POINT}"
df -i "${MOUNT_POINT}"
sudo lssu -a -l /dev/ram1

echo -e "\n\nDeleting files and directories"
delete_files

echo -e "\nDisk usage after deleting:"
for i in $(seq 1 20); do
    # Get the current date and time and log it
    echo "Checking usage at: $(date), i=$i" 
    
    ps aux | grep nilfs_cleanerd | grep -v grep
    
    # Run df -h and append the output to the log file
    df "${MOUNT_POINT}"
    df -h "${MOUNT_POINT}"
    df -i "${MOUNT_POINT}"
    sudo lssu -a -l /dev/ram1
    
    # Wait for the specified interval
    sleep 5
done



