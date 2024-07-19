#!/bin/bash

MOUNT_POINT="/mnt/test-nilfs2-i1-s0"
FILE_PREFIX="testfile"
DIR_PREFIX="testdir"
WRITE_DATA="This is a test string to fill up the filesystem. "
FILE_SIZE_MB=10
MIN_FREE_SPACE_MB=10
INTERVAL="1h"
LOGFILE="/home/ubuntu/Metis/fs-state/df_results.log"

COUNTER=0


get_free_space() {
  df --output=avail "$MOUNT_POINT" | tail -n 1
}

create_files() {
  
  for i in $(seq 1 100); do
    FREE_SPACE=$(get_free_space)
    if [ "$FREE_SPACE" -gt $((MIN_FREE_SPACE_MB * 1024)) ]; then
      COUNTER=$((COUNTER + 1))
      FILE="${FILE_PREFIX}_${i}"
      DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
      sudo mkdir "$DIR"
      sudo dd if=/dev/zero of="${DIR}/${FILE}" bs=1M count=${FILE_SIZE_MB} status=none
      echo "Created ${DIR}/${FILE}"  
      df -h "${MOUNT_POINT}" 
    else
      echo "Not enough space to create more files. Stopping." 
      break
    fi
  done
}

delete_files() {
  for i in $(seq 1 $COUNTER); do
    DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
    sudo rm -rf "$DIR"
    echo "Deleted ${DIR}" 
    df -h "${MOUNT_POINT}" 
  done
}


delete_cp() {
    cd ${MOUNT_POINT}
    echo "Checkpoints before removing" 
    lscp 
    CHECKPOINTS=($(lscp | awk 'NR>1 {print $1}'))
    for checkpoint in "${CHECKPOINTS[@]}"; do
        sudo rmcp "$checkpoint"
        if [ $? -eq 0 ]; then
            echo "Deleted checkpoint $checkpoint" 
        else
            echo "Failed to delete checkpoint $checkpoint" 
        fi
    done
    echo "Checkpoints after removing" 
    lscp 
    sudo nilfs_cleanerd
}



cd ~/Metis/fs-state
echo "Initial disk usage:" 
df -h "${MOUNT_POINT}" 

echo "Creating files and directories" 
create_files

echo "Deleting files and directories" 
delete_files 

echo "Delete snapshots and call cleanerd" 
delete_cp

echo "Disk usage after deleting everything at $(date):" 
df -h "${MOUNT_POINT}" 


# Convert hours to seconds

# Infinite loop to run df -h every N hours
while true; do
    # Get the current date and time and log it
    echo "Checking disk usage at: $(date)" 
    
    # Run df -h and append the output to the log file
    df -h "${MOUNT_POINT}" 
    
    # Wait for the specified interval
    sleep "${INTERVAL}"
done
