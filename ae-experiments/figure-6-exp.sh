#!/bin/bash

########### Figure 6: Metis performance with Swarm (distributed) verification ###########

rmmod brd

cd ../fs-state 

./loadmods.sh

yes | sudo sh -c 'cp -f swarm-fast24ae.lib swarm.lib'

make clean

./setup_swarm.sh -f ext4:256:ext2:256 -n 6

./mcfs-main.pml.swarm 

