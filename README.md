# Metis: File System Model Checking via Versatile Input and State Exploration

This is the artifact for the FAST '24 paper **"Metis: File System Model Checking 
via Versatile Input and State Exploration"**.  Metis is a
model-checking framework designed for versatile, thorough, yet
configurable file system testing in the form of input and state
exploration.

Metis was formerly known as MCFS (Model Checking File Systems).

## Table of Content

1. [Setup Metis and RefFS](#setup-metis-and-reffs)
   1. [OS ane Kernel Verison](#os-and-kernel-version)
   2. [Prerequisites and Required Artifacts ](#prerequisites-and-required-artifacts)
2. [FAST24 Artifact Evaluation](#fast24-artifact-evaluation)
   1. [Machines](#machines)
   2. [Kick-the-Tires - System Configuration and Test Run](#kick-the-tires---system-configuration-and-test-run)
       1. [Installation of dependencies](#installation-of-dependencies)
       2. [Simple Metis run to check Ext2 with Ext4](#simple-metis-run-to-check-ext2-with-ext4)
       3. [Set up RefFS](#set-up-reffs)  
       4. [Using Metis replayer](#using-metis-replayer)
       5. [Swarm Verification with single machine](#swarm-verification-with-single-machine)
   3. [Reproduction of Experimental Results](#reproduction-of-experimental-results)
       1. [Test Input Coverage (Figure 3, 4, 5)](#test-input-coverage-figure-3-4-5) 
       2. [Metis Performance and Scalability (Figure 6)](#metis-performance-and-scalability-figure-6)
       3. [RefFS Performance and Reliability (Figure 7)](#reffs-performance-and-reliability-figure-7)
       4. [Bug Finding](#bug-finding)
   4. [Troubleshooting](#troubleshooting)
         1. [Error message: ramdisk device issue](#error-message-ramdisk-device-issue)
         2. [Cannot compile RefFS and lack of mcfs header files](#cannot-compile-reffs-and-lack-of-mcfs-header-files)
3. [Major Components](#major-components)
    1. [driver-fs-state](#driver-fs-state)
    2. [fs-state](#fs-state)
    3. [fs_bugs](#fs_bugs)
    4. [kernel](#kernel)
    5. [scripts](#scripts)
    6. [other folders](#other-folders)
4. [Reference](#reference)
5. [Contact](#contact)

## Setup Metis and RefFS

### OS ane Kernel Verison

We tested Metis on Ubuntu 22.04 and Ubuntu 20.04 with Linux kernel versions 
specified in `./kernel` (i.e., 4.4, 4.15, 5.4, 5.15.0, 5.19.7, 6.0.6, 
6.2.12, 6.3.0, and 6.6.1).  
We cannot guarantee the functionality and usability on other 
Ubuntu or Linux kernel versions.  

### Prerequisites and Required Artifacts 

Metis is built on the top of the SPIN 
model checker and Swarm Verification.  Metis relies on a reference file 
system to check a file system under test, and we use RefFS or Ext4 as 
the reference file system.  Other file systems can also serve as the 
reference file systems.  Below shows the repositories/artifacts required by Metis:  

RefFS: https://github.com/sbu-fsl/fuse-cpp-ramfs  
fsl-spin (modified version of SPIN): https://github.com/sbu-fsl/fsl-spin  
swarm-mcfs (modified version of Swarm): https://github.com/sbu-fsl/swarm-mcfs  
IOCov (tool to compute input coverage for file system testing): https://github.com/sbu-fsl/IOCov  

Note that we must use `fsl-spin` for the SPIN model checker for Metis 
and `swarm-mcfs` for the Swarm Verification tool, and the vanilla SPIN/Swarm
cannot work with Metis.  Please check out each repository for respective 
documentation.  A number of 
general libraries and tools are also required.  
Please see `script/setup-deps.sh` for details.

To run [IOCov](https://github.com/sbu-fsl/IOCov), a few Python packages are required.
Please run the following command to install them (using Python 3 and pip3 as an example):

```bash
sudo apt-get install python3-pip
pip3 install numpy scipy matplotlib
```

## FAST24 Artifact Evaluation

Thank you for evaluating our artifact.  We have provided a set of machines, 
scripts, and instructions to help you set up Metis/RefFS and reproduce our experimental results.
If you encounter any issues, please feel free to contact us via HotCRP messages.
We will respond to your questions as soon as possible and definitely in 24 hours.

### Machines 

We have provided VMs for each AEC member.  TODO

### Kick-the-Tires - System Configuration and Test Run 

#### Installation of dependencies

We have configured the necessary environments on the machines provided 
to AEC members, so you don't need to set up environment by yourself.  
If you want to set up Metis on your own machine,
you can install Metis libraries (run `make && make install` on the root 
directory of Metis) first and use our `setup-deps.sh` bootstrap 
script (without sudo) to install all the dependencies including necessary 
libraries/tools, RefFS, and the modified version of SPIN/Swarm.

```bash 
cd Metis # your Metis root directory
make 
make install
cd scripts
./setup-deps.sh
```

#### Simple Metis run to check Ext2 with Ext4

You can run Metis with single verification task (VT) by the `setup.sh` script
in `./fs-state`.  Before executing `setup.sh`, you need to ensure the 
test devices for file systems are already created, and their device 
types/sizes are matching with the arguments provided to `setup.sh`.  We 
have provided the script to run a simple Ext4 vs. Ext2 experiment in Metis
where Ext4 serves as the reference file system and Ext2 is the file system 
under test.  To run this test

```bash
cd fs-state/mcfs_scripts/
sudo ./single_ext2.sh
```

This script will clean up resources, create devices, and run Metis with 
Ext4 vs. Ext2.  Note that this experiment will be continuously running 
until it encounters a discrepancy (i.e., potential bug) between two file 
systems.  It will be unlikely to have a discrepancy between Ext4 and 
Ext2, so this is only for demonstration purpose.  You can wait till the 
model checker ends (which takes weeks of time!) or press Ctrl+C or run
`fs-state/stop.sh` to abort 
the program half-way (which we highly recommend for this demo).

Metis logs serve as the critical role to identify, analyze and replay bugs and 
are saved under the `fs-state` folder.
As the model checker is running or terminated, the standard output is redirected to
`output-pan*.log` and the standard error is redirect to `error-pan*.log`. 
`output-pan*.log` records the timestamps, operations that have been performed, 
as well as the
arguments and results of each operation, and output abstract state. 
`error-pan*.log` logs the discrepancies
in behavior among the tested file systems that the model checker has
encountered.  There will also be a `sequence-pan-*.log` that records the 
sequence of file system
operations that have been performed by model checker in a easy-to-parse format.
We have a log rotation mechanism to
This is intended for the replayer to use.  If you want to delete all those logs,
you can run `make clean` under the `fs-state` folder.

#### Set up RefFS 

We also created a new RefFS as Metis's reference file system.
Please refer to the [RefFS repository](https://github.com/sbu-fsl/fuse-cpp-ramfs) and its
[README](https://github.com/sbu-fsl/fuse-cpp-ramfs/blob/master/README.md) regarding the 
installation and mount of RefFS.  

You can run RefFS vs. Ext4 by running the `single_verifs2.sh` script:

```bash
cd fs-state/mcfs_scripts/
sudo ./single_verifs2.sh
```

Again, this experiment can take a very long time to complete (weeks or months), so 
you can abort it half-way via Ctrl+C or running `fs-state/stop.sh`.  The experimental
logs of RefFS vs. Ext4 should appear in the `fs-state` folder.  The log file names show 
the timestamp and pid of the experiment. 

#### Using Metis replayer

After each experiment, we can use replayer to replay the exact sequence 
of operations to debug/reproduce the discrepancy/bug or obtain any intermediate 
file system state during a Metis run.  The Metis replayer parses the `sequence-pan*.log`
line by line, reads the operations/arguments, and perform the exact operations
on single or both file systems (specified by the replayer argument list).  
Let's use a previous Ext4 vs. Ext2 example to demonstrate Metis's replayer:

```bash
cd fs-state
make clean # clear all logs and object files
cd mcfs_scripts
sudo ./single_ext2.sh 
```

Then we abort the Metis process by Ctrl-C or running script `sudo ./stop.sh`.
We recommend to use `stop.sh` because we also need to unmount all the 
file systems used by Metis.  Using Ctrl-C needs to manually unmount all 
the test file systems (i.e., `umount /mnt/test-*` or `umount /dev/ram*`).
After that, we can get a sequence log file and a dump_prepopulate log file
in the `fs-state` folder. 
We use `sequence-pan-20231214-014909-2031206.log` and `dump_prepopulate_0.log` as an example.  

We need to ensure that test devices are created with the correct device
types/sizes.  For Ext4 vs. Ext2, you can run `loadmods.sh` in the `fs-state`
to create desired ramdisks.
To use the replayer, we should first open the `fs-state/replay.c` file, 
edit **line 29 and line 35** to reflect the log file names generated 
from a previous experiment that we want to replay.  Therefore, the 
replayer can use the correct log files to replay.  
After editing the `replay.c` file, we can compile the replayer by:

```bash 
cd fs-state
make replayer
```

We will get a `replay` binary executable.  We will run replayer with the 
following command.  The argument list shows `VTid:FS1:SIZE1:FS2:SIZE2`.

```bash 
sudo ./replay -K 0:ext4:256:ext2:256
```

The execution of file system operations will be printed on the console.  

#### Swarm Verification with single machine

Above experiments use one Metis process only, but Metis can run multiple 
processes (i.e., verification tasks or VTs) in parallel by virtue of Swarm 
Verification.  To support Swarm, we provide a configuration file `fs-state/swarm.lib`.
You can find the [detailed description](https://github.com/sbu-fsl/swarm-mcfs/blob/swarm-v2/README.md) 
of the configuration file.

To run a quick Metis experiment with Swarm for Ext4 vs. Ext2, please copy the 
`swarm-single-node.lib` to override `swarm.lib`, set up devices, run the `fs-state/setup_swarm.sh`
with proper arguments, and finally run the generated `mcfs-main.pml.swarm` script.

```bash
cd ./fs-state
# Use proper swarm.lib configuration file
yes | cp -f swarm-single-node.lib swarm.lib
make clean
# Unmount file systems if rmmod brd failed
sudo rmmod brd
sudo ./loadmods.sh
# Test Ext4 vs. Ext2 with 6 VTs
sudo ./setup_swarm.sh -f ext4:256:ext2:256 -n 6
# Run the final swarm driver
sudo ./mcfs-main.pml.swarm 
```

This will produce multiple VTs (pan), and each VT explores a different 
portion of the state space by various diversification techniques.
Make sure the number of VTs should be equal or fewer than the number of 
total CPU cores.  Every VT is independent and will produce its own 
logs.  Like single-VT Metis run, this experiment can last a very long 
time.  Please feel free to use `stop.sh` to stop all Metis Swarm VTs.
A more detailed document of Metis with Swarm Verification can be found 
at [here](fs-state/README-swarm.md).  Metis can also run VTs on multiple 
machines where each machine runs multiple VTs.  This is part of our 
evaluation results and can be found 
at [Metis Performance and Scalability](#metis-performance-and-scalability-figure-6).

### Reproduction of Experimental Results

#### Test Input Coverage (Figure 3, 4, 5)



##### Figure 3 Input Coverage open flags 40 minutes



##### Figure 4 Input Coverage write sizes 40 minutes

##### Figure 5 Input Coverage write sizes 4 hours


#### Metis Performance and Scalability (Figure 6)


#### RefFS Performance and Reliability (Figure 7)


#### Bug Finding


### Troubleshooting

#### Error message: ramdisk device issue

```
/dev/ram4 is not a block device.
Cannot setup ext4 because /dev/ram4 is bad or not ready.
Cannot setup file system ext4 (ret = -15)
pan3: ../common/log.c:77: do_write_log: Assertion `my_queue.data' failed.
Aborted (core dumped)
```

This error shows ramdisks are not setup correctly.  Please delete 
`/dev/ram*` if these ramdisks are not block devices (i.e., regular files).

```
find /dev -name 'ram*' ! -type b -exec rm -f {} \;
```

Then, you can call `sudo rmmod brd` to remove all the block-device ramdisks, and 
load the devices using our script or shell commands.

#### Cannot compile RefFS and lack of mcfs header files

```
/home/ubuntu/fuse-cpp-ramfs/src/pickle.cpp:3:10: fatal error: mcfs/errnoname.h: No such file or directory
    3 | #include <mcfs/errnoname.h>
      |          ^~~~~~~~~~~~~~~~~~
compilation terminated.
make[2]: *** [src/CMakeFiles/fuse-cpp-ramfs.dir/build.make:202: src/CMakeFiles/fuse-cpp-ramfs.dir/pickle.cpp.o] Error 1
make[1]: *** [CMakeFiles/Makefile2:145: src/CMakeFiles/fuse-cpp-ramfs.dir/all] Error 2
make: *** [Makefile:136: all] Error 2
Command './setup-deps.sh' exited with error (2).
```

Please go to the root directory of the Metis directory and do `make && make clean` to 
install Metis/MCFS libraries and header files.


## Major Components:

This repo consists of multiple folders.  Below are concise descriptions 
of each folder.

### driver-fs-state

The Metis model checker with input coverage driver that can achieve 
versatile input coverage.  Note that most of code in this folder is 
reused from the `fs-state` folder but with input coverage support 
via multiple macros.

### fs-state

The main folder of the Metis model checker.
This checker will run a set of file system operations (system calls)
non-deterministically on multiple file systems, and then compare their
behavior. If there's any discrepancy, the checker will log it.

Please enter the folder to see detailed document and code.

### fs_bugs

Reproducers we developed for the bugs we found by Metis.  Check out each 
file system folder for details.

### kernel

Kernel modules (modified `brd` driver or `brd2`) that helps the file system model checker
to create ramdisks with desired sizes.  Use the correct `brd2` version based on 
your Linux kernel version.

### scripts

Various scripts to set up Metis and RefFS, analyze Swarm Verification 
results from Metis, code coverage investigation, etc.

### other folders

For the explanation of other folders, please refer to this [README](./other-folders.md).

## Reference 

## Contact 
For any question, please feel free to contact Yifei Liu ([yifeliu@cs.stonybrook.edu](mailto:yifeliu@cs.stonybrook.edu))
and Erez Zadok ([ezk@cs.stonybrook.edu](mailto:ezk@cs.stonybrook.edu)).
