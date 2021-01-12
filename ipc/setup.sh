#!/bin/bash

umount -f /mnt/test-ext4
fusermount -u /mnt/test-crmfs

dd if=/dev/zero of=/dev/ram0 bs=1k count=256
mkfs.ext4 -F /dev/ram0
# mount -t ext4 -o rw,noatime /dev/ram0 /mnt/test-ext4
rm -rf /mnt/test-ext4/lost+found
./crmfs /mnt/test-crmfs

