#!/bin/bash

pkill -9 -f "./demo.pml"
pkill -9 -f "sh ./script"
pkill -9 -f "./pan"
umount /dev/ram*
