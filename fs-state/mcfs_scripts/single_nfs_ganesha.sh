#!/bin/bash

NFS_GANESHA_EXT4_SZKB=256
EXT4_SZKB=256 

cd ..
sudo ./stop.sh
sudo rmmod brd

# If Ext4 has the same size as Ext2
if [ "$NFS_GANESHA_EXT4_SZKB" -eq "$EXT4_SZKB" ]; then
    sudo ./loadmods.sh
else
    cd ../kernel/brd-for-$(uname -r)
    make -C /lib/modules/$(uname -r)/build M=$(pwd)
    sudo insmod brd.ko rd_nr=2 rd_sizes=$NFS_GANESHA_EXT4_SZKB,$EXT4_SZKB
    cd ../../fs-state/
fi

sudo ./setup.sh -f nfs-ganesha-ext4:$NFS_GANESHA_EXT4_SZKB:ext4:$EXT4_SZKB
