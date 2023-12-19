#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

umount -f /mnt/test-ext4
fusermount -u /mnt/test-verifs1

dd if=/dev/zero of=/dev/ram0 bs=1k count=256
mkfs.ext4 -F /dev/ram0
# mount -t ext4 -o rw,noatime /dev/ram0 /mnt/test-ext4
rm -rf /mnt/test-ext4/lost+found
./crmfs /mnt/verifs1

