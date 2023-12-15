#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

KERNEL_SRC="/mcfs/Linux_Kernel_Install/linux-6.3"

# Enter into NILFS2 source code directory
cd $KERNEL_SRC/fs/nilfs2

rmmod nilfs2.ko

make -C /lib/modules/$(uname -r)/build M=$(pwd)

insmod nilfs2.ko
