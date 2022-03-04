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
	runcmd make install ARGS=$i;
	count=0
	for j in $(grep -Po '\t.*:\d+( |\t)' swarm.lib); do
		if [ $count -ge 1 ]; then
			remote=$(echo $j | awk -F ':' '{print $1}');

			scp libsmcfs$i.a "$remote":libsmcfs$i.a;
			if [ $num_pan -eq $i ];then
				scp parameters.pml "$remote":parameters.pml;
				scp Makefile "$remote":Makefile;
				scp 'stop.sh' "$remote":'stop.sh'
				ssh "$remote" "sh ./nfs-validator/fs-state/loadmods.sh" &
			fi
		fi
		count=$((count+1));
	done
done

runcmd swarm swarm.lib -f demo.pml
runcmd ./demo.pml.swarm

