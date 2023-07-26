#!/bin/bash

pkill -9 -f "./mcfs-main.pml"
pkill -9 -f "./mcfs-main.pml.swarm"
pkill -9 -f "sh ./script"
pkill -9 -f "./pan"
umount /dev/ram*
umount /dev/mtdblock*
umount /mnt/test-*
