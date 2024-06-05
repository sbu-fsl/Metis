#!/bin/bash

# Define the export path
export_path="/mnt/test-nfs-ganesha-export"

# Kill all NFS-Ganesha server processes
echo "Terminating all NFS-Ganesha server processes..."
pgrep ganesha | xargs sudo kill -9

# Check for any remaining NFS-Ganesha processes and terminate them
if pgrep ganesha; then
    pgrep ganesha | xargs sudo kill -9
fi

echo "All NFS-Ganesha processes terminated."

# Unmount all NFS mounts associated with NFS-Ganesha
echo "Unmounting all NFS file systems..."
mount | grep 'type nfs' | awk '{ print $3 }' | while read -r mountpoint; do
    echo "Unmounting $mountpoint..."
    sudo umount -f $mountpoint
done

# Unmount the export path
echo "Unmounting the NFS-Ganesha export path..."
sudo umount -f $export_path

echo "All NFS file systems and export path have been unmounted."

