#!/bin/bash

SERVER_MNT_DIR="/mnt/test-nfs-ganesha-export"
CLIENT_MNT_DIR="/mnt/test-nfs-ganesha-ext4-i0-s0"
EXT4_LOOP=$(losetup -f)
LOOP_FILE="/tmp/loopback_file_nfs.img"
LOOP_SIZE=1536 # in KiB

if [ -z "$EXT4_LOOP" ]; then
  echo "No free loop device found."
  exit 1
fi

# Create a file of the defined size using bs=1K
dd if=/dev/zero of="$LOOP_FILE" bs=1K count=$LOOP_SIZE

# Associate the loop device with the file
losetup "$EXT4_LOOP" "$LOOP_FILE"

# Check if the mount point is already mounted, unmount it
if test -n "$(mount | grep $SERVER_MNT_DIR)" ; then
    umount $SERVER_MNT_DIR || exit $?
fi

# Check if the mount point is already mounted, unmount it
if test -n "$(mount | grep $CLIENT_MNT_DIR)" ; then
    umount $CLIENT_MNT_DIR || exit $?
fi

# Remove mount point if not created, and create it again
if test -d $SERVER_MNT_DIR ; then
    rm -r $SERVER_MNT_DIR
fi

# Remove mount point if not created, and create it again
if test -d $CLIENT_MNT_DIR ; then
    rm -r $CLIENT_MNT_DIR
fi

# Create mount points and set permissions
mkdir -p $SERVER_MNT_DIR || { echo "Failed to create directory $SERVER_MNT_DIR"; exit $?; }
mkdir -p $CLIENT_MNT_DIR || { echo "Failed to create directory $CLIENT_MNT_DIR"; exit $?; }
chmod 755 $SERVER_MNT_DIR || { echo "Failed to set permissions for $SERVER_MNT_DIR"; exit $?; }
chmod 755 $CLIENT_MNT_DIR || { echo "Failed to set permissions for $CLIENT_MNT_DIR"; exit $?; }

# Create an Ext4 filesystem on the ramdisk
mkfs.ext4 $EXT4_LOOP || { echo "Failed to create Ext4 filesystem on $EXT4_LOOP"; exit $?; }
mount $EXT4_LOOP $SERVER_MNT_DIR || { echo "Failed to mount $EXT4_LOOP on $SERVER_MNT_DIR"; exit $?; }

# Start NFS-Ganesha server
systemctl start nfs-ganesha 

# Mount the NFS-Ganesha export on the client
mount.nfs4 -o vers=4 127.0.0.1:$SERVER_MNT_DIR $CLIENT_MNT_DIR

# Using "df -h" or a C program (statfs) to check the size of the mounted filesystem 
df -h
# make
# ./ganesha-small-dev

umount $CLIENT_MNT_DIR

dbus-send --system --type=method_call --print-reply --dest=org.ganesha.nfsd /org/ganesha/nfsd/ExportMgr org.ganesha.nfsd.exportmgr.RemoveExport uint16:77 

umount $SERVER_MNT_DIR

systemctl stop nfs-ganesha

# Detach the loop device
losetup -d "$EXT4_LOOP"
echo "Loop device $EXT4_LOOP detached"

# Clean up
rm -f "$LOOP_FILE"
echo "File $LOOP_FILE removed"
