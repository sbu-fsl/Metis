#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder
# Require apt-get install nilfs-tools
# Ensure that brd2 version is consistent with current kernel version

EXT4_SZKB=256
NILFS2_SZKB=1028

cd ..
sudo ./stop.sh

cd ../kernel/brd-for-6.3.0
sudo rmmod brd
make -C /lib/modules/$(uname -r)/build M=$(pwd)
sudo insmod brd.ko rd_nr=2 rd_sizes=$EXT4_SZKB,$NILFS2_SZKB
cd ../../fs-state/
sudo ./setup.sh -f ext4:$EXT4_SZKB:nilfs2:$NILFS2_SZKB
