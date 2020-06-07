#/bin/bash

IMGFILE="fs0.img"
BLOCKSIZE=1k
COUNT=256

# Create disk image file
sudo dd if=/dev/zero of=/tmp/$IMGFILE bs=$BLOCKSIZE count=$COUNT

# Detach unmounted loop devices
sudo losetup -D

# Setup loop device
LOOPDEV=$(sudo losetup --show -f /tmp/$IMGFILE)

# Format the image
sudo mkfs.ext4 $LOOPDEV

# Mount
sudo umount -f /mnt/test-ext4
sudo rm -rf /mnt/test-ext4
sudo mkdir -p /mnt/test-ext4
sudo mount -t ext4 -o sync $LOOPDEV /mnt/test-ext4

# Run test program
make
sudo ./pan | tee output.log

# Unset
echo "unmount"
sudo umount -f /mnt/test-ext4
# Detach loop device
echo "detach"
sudo losetup -d $LOOPDEV
# Remove image
echo "rm"
sudo rm /tmp/$IMGFILE

