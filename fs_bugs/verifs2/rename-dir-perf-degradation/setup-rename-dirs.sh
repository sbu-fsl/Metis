#!/bin/bash

EXT4_MNT_DIR="/mnt/ext4-rename-test"
VERIFS2_MNT_DIR="/mnt/verifs2-rename-test"
EXT4_DEV="/dev/ram0"
EXT4_SZKB=2048

# Setup and mount Ext4
if test -n "$(mount | grep $EXT4_MNT_DIR)" ; then
    umount $EXT4_MNT_DIR || exit $?
fi

if test -d $EXT4_MNT_DIR ; then
    rm -rf $EXT4_MNT_DIR
fi
mkdir -p $EXT4_MNT_DIR

# Check if brd ramdisk is loaded, if not, load it
if test -z "$(lsmod | grep brd)" ; then
    modprobe brd rd_nr=1 rd_size=$EXT4_SZKB
else
    modprobe -r brd
    modprobe brd rd_nr=1 rd_size=$EXT4_SZKB
fi

mkfs.ext4 $EXT4_DEV
mount -t ext4 $EXT4_DEV $EXT4_MNT_DIR

# Setup and mount VeriFS2
if test -n "$(mount | grep $VERIFS2_MNT_DIR)" ; then
    umount $VERIFS2_MNT_DIR || exit $?
fi

if test -d $VERIFS2_MNT_DIR ; then
    rm -rf $VERIFS2_MNT_DIR
fi
mkdir -p $VERIFS2_MNT_DIR

mount -t fuse.fuse-cpp-ramfs verifs2 $VERIFS2_MNT_DIR

# Populate same files/dirs to both Ext4 and VeriFS2 for BASIC renaming dir experiments
# dir4 and dir5 does not exit

# # For Ext4
# mkdir -p $EXT4_MNT_DIR/dir1/filled_subdir1
# mkdir -p $EXT4_MNT_DIR/dir1/filled_subdir2

# mkdir -p $EXT4_MNT_DIR/dir2/filled_subdir2
# mkdir -p $EXT4_MNT_DIR/dir2/filled_subdir3

# mkdir -p $EXT4_MNT_DIR/dir3/empty_subdir3
# mkdir -p $EXT4_MNT_DIR/dir3/empty_subdir4
# mkdir -p $EXT4_MNT_DIR/dir3/empty_subdir5

# touch $EXT4_MNT_DIR/dir1/filled_subdir1/file1
# touch $EXT4_MNT_DIR/dir1/filled_subdir2/file2
# mkdir -p $EXT4_MNT_DIR/dir2/filled_subdir2/subdir2
# touch $EXT4_MNT_DIR/dir2/filled_subdir3/file3

# # For VeriFS2
# mkdir -p $VERIFS2_MNT_DIR/dir1/filled_subdir1
# mkdir -p $VERIFS2_MNT_DIR/dir1/filled_subdir2

# mkdir -p $VERIFS2_MNT_DIR/dir2/filled_subdir2
# mkdir -p $VERIFS2_MNT_DIR/dir2/filled_subdir3

# mkdir -p $VERIFS2_MNT_DIR/dir3/empty_subdir3
# mkdir -p $VERIFS2_MNT_DIR/dir3/empty_subdir4
# mkdir -p $VERIFS2_MNT_DIR/dir3/empty_subdir5

# touch $VERIFS2_MNT_DIR/dir1/filled_subdir1/file1
# touch $VERIFS2_MNT_DIR/dir1/filled_subdir2/file2
# mkdir -p $VERIFS2_MNT_DIR/dir2/filled_subdir2/subdir2
# touch $VERIFS2_MNT_DIR/dir2/filled_subdir3/file3

echo "All rename setup setup done!"

# Compile and run the C program
make 
./rename-dirs-assert
