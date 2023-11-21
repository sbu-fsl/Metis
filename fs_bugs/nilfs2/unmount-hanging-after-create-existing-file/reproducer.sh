#!/bin/bash

MNTPNT="/mnt/test-nilfs2"
IMGFILE="./nilfs2-dev-88-unmount-hanging.img"

# Recompile NILFS2 kernel module
# ./recompile_nilfs2_mod.sh

# Mount an existing image to create a NILFS2 filesystem
./mount_nilfs2_img.sh $MNTPNT $IMGFILE

# Create an already-existing file to reproduce the unmount hanging bug
cd $MNTPNT/d-00
touch f-02
cd -

echo "Start Unmounting..."

# Unmounting to reproduce hanging
umount $MNTPNT

echo "Reproducer finished (not supposed to see this message due to hanging)."
