#!/bin/bash

MOUNT_POINT="/mnt/test-nilfs2-i2-s0"
FILE_PREFIX="testfile"
DIR_PREFIX="testdir"
WRITE_DATA="This is a test string to fill up the filesystem. "
FILE_SIZE=10
MIN_FREE_SPACE=30

get_free_space() {
  df --output=avail "$MOUNT_POINT" | tail -n 1
}

create_files() {

  for i in $(seq 1 10); do
    FREE_SPACE=$(get_free_space)
    echo "Free space: ${FREE_SPACE}"
    if [ "$FREE_SPACE" -gt $((MIN_FREE_SPACE * 1024)) ]; then
      FILE="${FILE_PREFIX}_${i}"
      DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
      sudo mkdir "$DIR"
      sudo dd if=/dev/zero of="${DIR}/${FILE}" bs=1M count=${FILE_SIZE} status=none
      echo "Created ${DIR}/${FILE}"
      df -h "${MOUNT_POINT}"
    # elif [ "$FREE_SPACE" -gt 20 ]; then
    #   FILE="${FILE_PREFIX}_${i}"
    #   DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
    #   sudo mkdir "$DIR"
    #   sudo dd if=/dev/zero of="${DIR}/${FILE}" bs=1K count=10 status=none
    #   echo "Created ${DIR}/${FILE} with 10 KB"
    #   sleep 1s
    #   df -h "${MOUNT_POINT}"
    else
      echo "Not enough space to create more files. Stopping."
      break
    fi
  done
}

delete_files() {
  for i in $(seq 1 10); do
    DIR="${MOUNT_POINT}/${DIR_PREFIX}_${i}"
    sudo rm -rf "$DIR"
    echo "Deleted ${DIR}"
    df -h "${MOUNT_POINT}"
  done
}

echo "Creating files and directories"
create_files

sleep 10s
df -h "${MOUNT_POINT}"

echo "Deleting files and directories"
delete_files

echo "Final disk usage:"
df -h "${MOUNT_POINT}"
