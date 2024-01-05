#!/bin/bash

########### 1st script of Figure 6: Metis performance with Swarm (distributed) verification ###########
TERMTIME="13h"
VTNUM=6
SWARM_SCRIPT="mcfs-main.pml.swarm"

cd ../fs-state 

sudo ./stop.sh
sudo rmmod brd
sudo ./loadmods.sh

yes | sudo sh -c 'cp -f swarm-fast24ae.lib swarm.lib'

sudo make clean

sudo ./setup_swarm.sh -f ext4:256:ext2:256 -n $VTNUM

# Replace "sh ./${" pattern to "sudo sh ./${"

if ! grep -q "sudo sh \./" $SWARM_SCRIPT; then
    sed -i 's|sh \./\${|sudo sh \./\${|g' $SWARM_SCRIPT
fi

sudo ./mcfs-main.pml.swarm &

# Wait for 13 hours
sleep $TERMTIME

# Call stop script twice for each machine to make sure all resources (e.g., mounted devices) are clean up
sudo ./stop.sh
sudo ./stop.sh
ssh metis-ae1-swarm1 'sudo /home/cc/stop.sh'
ssh metis-ae1-swarm1 'sudo /home/cc/stop.sh'
ssh metis-ae1-swarm2 'sudo /home/cc/stop.sh'
ssh metis-ae1-swarm2 'sudo /home/cc/stop.sh'
