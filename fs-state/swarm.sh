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


runcmd make parameters
scp parameters.pml "$remote":parameters.pml
# use for loop to run a command 4 times with different number in the command
for (( i=1; i<=$num_pan; i++ )); do
	runcmd make install ARGS=$i;
	scp libsmcfs$i.a "$remote":libsmcfs$i.a;
done

runcmd swarm swarm.lib -f demo.pml
runcmd ./demo.pml.swarm
