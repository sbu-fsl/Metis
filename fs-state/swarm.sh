#!/bin/bash

WD=$(pwd)
verbose=0
num_pan=4
remote=$(grep -Po '\t.*:\d+( |\t)' swarm.lib | awk '{print $2}' | awk -F ':' '{print $1}')

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

# use for loop to run a command 4 times with different number in the command
for i in {1..4}; do
	runcmd make install ARGS=$i;
done

runcmd echo "copying dependencies to $remote..."

scp libsmcfs1.a "$remote":libsmcfs1.a
scp libsmcfs2.a "$remote":libsmcfs2.a
scp libsmcfs3.a "$remote":libsmcfs3.a
scp libsmcfs4.a "$remote":libsmcfs4.a


runcmd swarm swarm.lib -f demo.pml
runcmd ./demo.pml.swarm

