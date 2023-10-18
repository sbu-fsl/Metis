#!/bin/bash

modprobe brd rd_nr=32 rd_size=512
modprobe mtdram total_size=512 erase_size=16
modprobe mtdblock
