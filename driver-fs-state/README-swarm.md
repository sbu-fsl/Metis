# Swarm verification

## What is Swarm?

Swarm verification runs multiple Spin model checker instances in parallel.  By
tuning compilation and command-line parameters of these model checker instances,
such as specifying different searching techniques and using different random
seeds, they will explore diverse portions of the large state space independently.
Thus, Swarm covers the state space much faster through parallelism.

For detailed explanation of the Swarm verification algorithm, please see this
paper: [Swarm Verification](http://spinroot.com/gerard/pdf/ASE2008_HJG.pdf)

Evaluation of Swarm verification:
[Cloud-Based Verification of Concurrent Software](http://spinroot.com/gerard/pdf/vmcai2016.pdf)

## Adaptions

MCFS is a lot more than an ordinary model checker as it intensively interacts
with the real operating systems and file systems via system calls.  Swarm, on
the other hand, expects the model checkers it drives to be built and executed
with basic commands like `spin -a model.pml; gcc -o pan pan.c; ./pan`.

As a result, the stock version of Swarm does not support the special building
and setup procedures that MCFS needs, which is why we made changes to both MCFS
and Swarm in order to let MCFS take advantage of the parallelism that Swarm
offers.

### Changes to MCFS

Reference: https://github.com/sbu-fsl/nfs-validator/commits/swarm-xxh

#### Adjustable config header

If the macro `CONFIG_H` is defined during compilation, MCFS will include what's
defined in `CONFIG_H` as the config header instead of the default `config.h`.

#### Setup functions instead of setup script

#### Exponential backoff on busy unmounting

### Changes to Swarm

Reference: https://github.com/sbu-fsl/swarm-mcfs/commits/for-mcfs

1. When building the model checker, use `make` instead of `cc`. Also defines
   `CONFIG_H`.

2. Change the name of the executable to `swarm-mcfs` to distinguish from the
   stock version.

3. Also redirects stderr output to files

## Current Status

Currently we support using Swarm to run 4 MCFS instances in parallel to check
Ext4 vs. Ext2 on a single machine.  I also tried Swarm's distributed setting,
but encountered some issues and therefore it is not yet completely supported.

## How to run?

### Single machine, 4 cores, Ext4 vs. Ext2

1. Make sure the `brd` kernel module is loaded and has at least 8 256KB RAM
   block devices named `/dev/ram0` to `/dev/ram7` (Can be done by running
   `loadmods.sh`).

2. Make sure you have the latest `swarm-mcfs` and `fsl-spin` installed.

3. Under this directory, run `swarm-mcfs -c4 -f mcfs-main.pml`. `-c4` means using 4
   CPU cores, and `-f model.pml` specifies the Promela model.  It is also
   recommended to run this under Screen or tmux.

4. It should start to run and you can see the logs.

### Distributed settings on multiple machines (Updated on 07/21/2023 by Yifei)

***Swarm/MCFS master and client setup:***

Before running Swarm verification on multiple machines, we need to specify 
a machine as the "master" of all Swarm nodes.  Master machine is the one to 
send the scripts and all the files required to compile pan verifiers 
to all other clients machines via ssh/scp.

For the case of 6 VTs for one master machine and two client machines, 18 VTs in total,
the master machine will compile 6 pan verififers (pan1-pan6) and create 18 "scripts" (script0-script17).
After sending files to client machines, all these clients will run `mcfs-main.pml.swarm` file and 
compile the 6 pan verifiers again and run scripts to start VTs.
Every script uses only one dedicate pan verifier --- script0/6/12 uses pan1, script5/11/17 uses pan6, etc.
Every pan execution command (`./pan*`) uses different random seed (`-RS`).

***Prerequisites:***

1. On the master machine, we need to edit the `cpus` field of the `swarm.lib` 
   file.  Specify the hostname **(as shown in `vim ~/.ssh/config` in the master machine and the `hostname` in the client machines)** 
   and number of VTs for each machine.  
   For example, `cpus	6	yifeilatest4:6       yifeilatest5:6 # nr available cpus (exact)`

2. Double-check if the `hostname` on the client machines are correct.  If not,
   run command `sudo hostname new-server-name-here` and edit `/etc/hostname`.
   We can change the `hostname` without restarting the machine.  We may need to 
   edit `/etc/hosts` as well.

3. Make sure the master machine can connect to all the other client machines
   via ssh without password.  If not yet, use `ssh-copy-id` to copy ssh keys
   to other clients.

3. Make sure the client machines have `nfs4mc` repo in the root directory

4. Make sure all the machines have installed MCFS libraries --- go to `nfs4mc`
   directory, and do `make` and `make install`.

5. Make sure all the machines have the devices ready for mounting the file
   systems under testing with correct sizes (we no longer run the load device scripts
   remotely by `setup_swarm.sh`).  If we want to test VeriFS,
   we need to install the VeriFS on the machines first.

Examples of editting directories for remote machines as follows

Example of `setup_swarm.sh`:
```bash
REMOTEDIR="/mcfs-swarm/"
# Use ssh and scp to set up swarm for remotes
count=0
for i in $(grep -Po '\t.*:\d+( |\t)' ${SWARM_CONF}); do
	if [ $count -ge 1 ]; then
		remote=$(echo $i | awk -F ':' '{print $1}');
		scp libsmcfs.a "$remote":${REMOTEDIR}libsmcfs.a;
		scp parameters.pml "$remote":${REMOTEDIR}parameters.pml;
		scp Makefile "$remote":${REMOTEDIR}Makefile;
		scp 'stop.sh' "$remote":${REMOTEDIR}'stop.sh'
		# ssh "$remote" "sh ./nfs-validator/fs-state/loadmods.sh" &
		if [ "$USE_ENV_VAR" = "1" ]; then
			for (( j=1; j<=$NUM_PAN; j++ )); do
				ssh "$remote" "MCFS_FSLIST$j=$MCFSLIST"
			done
		fi
	fi
	count=$((count+1));
done
```

Example of `mcfs-main.pml.swarm`:
```bash
# start up the remote executions:
case `hostname` in
	yifeilatest5)
		;;
	yifeilatest4)
		;;
	*)
		scp mcfs-main.pml yifeilatest5:../mcfs-swarm/mcfs-main.pml
		scp mcfs-main.pml.swarm yifeilatest5:../mcfs-swarm/mcfs-main.pml.swarm
		if [ $XEC -eq 0 ]
		then
			ssh -p 130 yifeilatest5 "cd /mcfs-swarm/ && sh ./mcfs-main.pml.swarm prep" &
		else
			ssh -p 130 yifeilatest5 "cd /mcfs-swarm/ && sh ./mcfs-main.pml.swarm" &
		fi
		scp mcfs-main.pml yifeilatest4:../mcfs-swarm/mcfs-main.pml
		scp mcfs-main.pml.swarm yifeilatest4:../mcfs-swarm/mcfs-main.pml.swarm
		if [ $XEC -eq 0 ]
		then
			ssh -p 130 yifeilatest4 "cd /mcfs-swarm/ && sh ./mcfs-main.pml.swarm prep" &
		else
			ssh -p 130 yifeilatest4 "cd /mcfs-swarm/ && sh ./mcfs-main.pml.swarm" &
		fi
		;;
esac
```

***Steps of running Swarm verification on multiple machines:*** 

Before running swarm, make sure the environment is clean.  May need to do `make clean`.

1. Modify `REMOTEDIR` variable in `setup_swarm.sh`.

2. Run corresonding swarm in `/mcfs_scripts`, e.g., running `./swarm_verifs2.sh` for 
   running swarm with Ext4 vs. VeriFS2.  Make sure setting the number of VTs and device sizes, 
   and using the correct load device script.  The `./swarm_verifs2.sh` scripts calls 
   `setup_swarm.sh` script where `./mcfs-main.pml.swarm` will not be executed by default.

3. After running `./swarm_verifs2.sh`, edit the generated `mcfs-main.pml.swarm` file for 
   using the correct ssh/scp commands and remote directories.
   (we can copy from `README-swarm.md` -- Example of `mcfs-main.pml.swarm`)

4. Run `mcfs-main.pml.swarm` by `./mcfs-main.pml.swarm` on the master machine.  Swarm should 
   be running on the master and all the other client machines.

## Troubleshooting

### swarm: no pan.c; cannot proceed
Use `ssh -p 130 yifeilatest5 "cd /mcfs-swarm/ && sh ./mcfs-main.pml.swarm" &` instead 
of `ssh -p 130 yifeilatest5 "sh /mcfs-swarm/mcfs-main.pml.swarm" &` because the default 
directory to run shell script on remote machines is root (`~/`) and we need to change
directory to the one has those files (`cd /mcfs-swarm/`) first.


## How to evaluate?

## Limitations and issues
