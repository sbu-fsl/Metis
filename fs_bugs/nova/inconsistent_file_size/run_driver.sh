#!/bin/bash

DRIVER_LOOP_MAX=100000000

NOVA_MNT_DIR="/mnt/novatest"
PMEM_DEVICE="/dev/pmem0"

if test -n "$(mount | grep $PMEM_DEVICE)" ; then
    umount $PMEM_DEVICE || exit $?
fi

if test -d $NOVA_MNT_DIR ; then
    rm -rf $NOVA_MNT_DIR
fi
mkdir -p $NOVA_MNT_DIR

./driver $NOVA_MNT_DIR $PMEM_DEVICE ./cbuf-nova-state-3221-seq-9968-ckpt-0.img $DRIVER_LOOP_MAX
