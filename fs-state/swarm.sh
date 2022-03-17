#!/bin/bash

WD=$(pwd)
verbose=0
num_pan=4

runcmd() {
	if [ "$verbose" != "0" ]; then
		echo ">>> $@" >&2 ;
        fi
	sleep 0.5;
	$@;
	ret=$?;
	if [ $ret -ne 0 ]; then
		echo "Command '$0' exited with error ($ret)." >&2;
		exit $ret;
	fi
}

runcmd make parameters
# use for loop to run a command 4 times with different number in the command
for (( i=1; i<=$num_pan; i++ )); do
	# THIS OVERRIDES OTHER BINARIES
	runcmd make install ARGS=$i;
done

MCFSLIST="ext4:256:ext2:256"
export MCFS_FSLIST1="$MCFSLIST" MCFS_FSLIST2="$MCFSLIST" MCFS_FSLIST3="$MCFSLIST" MCFS_FSLIST4="$MCFSLIST"

runcmd swarm swarm.lib -f demo.pml
runcmd ./demo.pml.swarm

