#!/bin/bash

modprobe brd rd_nr=32 rd_size=256
modprobe mtdram total_size=256 erase_size=16
modprobe mtdblock
