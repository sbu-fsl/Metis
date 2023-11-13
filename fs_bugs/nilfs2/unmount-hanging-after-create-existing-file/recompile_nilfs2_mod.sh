#!/bin/bash

KERNEL_SRC="/mcfs/Linux_Kernel_Install/linux-6.3"

# Enter into NILFS2 source code directory
cd $KERNEL_SRC/fs/nilfs2

rmmod nilfs2.ko

make -C /lib/modules/$(uname -r)/build M=$(pwd)

insmod nilfs2.ko
