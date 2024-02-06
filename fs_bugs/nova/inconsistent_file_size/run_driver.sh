#!/bin/bash

DRIVER_LOOP_MAX=10000000

NOVA_MNT_DIR="/mnt/novatest"
PMEM_DEVICE="/dev/pmem0"

if test -n "$(mount | grep $PMEM_DEVICE)" ; then
    umount $PMEM_DEVICE || exit $?
fi

if test -d $NOVA_MNT_DIR ; then
    rm -rf $NOVA_MNT_DIR
fi
mkdir -p $NOVA_MNT_DIR

modprobe nova

./driver $NOVA_MNT_DIR $PMEM_DEVICE $DRIVER_LOOP_MAX
