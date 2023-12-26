# Metis: File System Model Checking via Versatile Input and State Exploration

This is the artifact for the FAST '24 paper **"Metis: File System Model Checking 
via Versatile Input and State Exploration"**.  Metis is a differential-testing based
model-checking framework designed for versatile, thorough, yet
configurable file system testing in the form of input and state
exploration.  Metis can find bugs in file systems with support of fast 
bug reproduction and debugging.  

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
4. [Citation](#citation)
5. [Contact](#contact)

## Setup Metis and RefFS

### OS ane Kernel Verison

We tested Metis on Ubuntu 22.04 and Ubuntu 20.04 with Linux kernel versions 
specified in `./kernel` (i.e., 4.4, 4.15, 5.4, 5.15.0, 5.19.7, 6.0.6, 
6.2.12, 6.3.0, and 6.6.1). We cannot guarantee the functionality and usability on other 
Ubuntu or Linux kernel versions.  

### Prerequisites and Required Artifacts 

Metis is built on the top of the SPIN 
model checker and Swarm Verification.  Metis relies on a reference file 
system to check a file system under test, and we use RefFS or Ext4 as 
the reference file system.  Other file systems can also serve as the 
reference file systems.  Below shows the repositories/artifacts required by Metis:  

RefFS: https://github.com/sbu-fsl/RefFS  
IOCov (tool to compute input coverage for file system testing): https://github.com/sbu-fsl/IOCov  
fsl-spin (modified version of SPIN): https://github.com/sbu-fsl/fsl-spin  
swarm-mcfs (modified version of Swarm): https://github.com/sbu-fsl/swarm-mcfs  

Note that we must use `fsl-spin` for the SPIN model checker for Metis 
and `swarm-mcfs` for the Swarm Verification tool, and the vanilla SPIN/Swarm
cannot work with Metis.  Please check out each repository for respective 
documentation.  A number of 
general libraries and tools are also required. Please see `script/setup-deps.sh` for details.

To run [IOCov](https://github.com/sbu-fsl/IOCov), a few Python packages are required.
Please run the following command to install them (using Python 3 and pip3 as an example):

```bash
sudo apt-get install python3-pip
sudo pip3 install numpy scipy matplotlib
```

## FAST24 Artifact Evaluation

Thank you for evaluating our artifact.  We have provided a set of machines, 
scripts, and instructions to help you set up Metis/RefFS and reproduce our experimental results.
***If you encounter any issues, please feel free to contact us via HotCRP messages.***
We will respond to your questions as soon as possible and definitely in 24 hours.

### Machines 

We have provided bare metal machines for AE reviewers. TODO




Note that some experiments can take a long time.  We recommend you to run 
experiments under `tmux` or `screen` so that you can detach the terminal without
interrupting any running long experiment.  I configured `tmux` using my 
[own config file](https://github.com/Yifei-Liu/yf-config-files/blob/master/.tmux.conf).
Feel free to choose another one as you like.  

### Kick-the-Tires - System Configuration and Test Run 

#### Installation of dependencies

We have configured the necessary environments on the machines provided 
to AEC members, so you **don't** need to set up environment by yourself.  
If you really want to set up the Metis environment on by yourself (e.g., on your own machines), 
after setting up ssh keys with Github, you can clone our repo:

```bash
git clone git@github.com:sbu-fsl/Metis.git
```

Next, you need to use our `setup-deps.sh` bootstrap 
script (without sudo) to install all the dependencies including necessary 
libraries/tools and the modified version of SPIN/Swarm:

```bash
cd ~/Metis/scripts
./setup-deps.sh
```

Then, you need to install Metis libraries by running `make && make install` on the root 
directory of Metis, which is required by RefFS:

```bash
cd ~/Metis # your Metis root directory
make 
make install
```

Finally, you can install RefFS by following commands:
  
```bash
cd ~
git clone git@github.com:sbu-fsl/RefFS.git
cd RefFS
./setup_verifs2.sh 
```

Using `mount | grep mnt`, you will see RefFS (aka. VeriFS2) is mounted on `/mnt/test-verifs2`.
You can unmount it by `sudo umount /mnt/test-verifs2`.  We will use RefFS as the reference file system
in some experiments.

#### Simple Metis run to check Ext2 with Ext4

You can run Metis with single verification task (VT) by the `setup.sh` script
in `./fs-state`.  Before executing `setup.sh`, you need to ensure the 
test devices for file systems are already created, and their device 
types/sizes are matching with the arguments provided to `setup.sh`.  We 
have provided the script (`single_ext2.sh`) to run a simple Ext4 vs. Ext2 experiment in Metis
where Ext4 serves as the reference file system and Ext2 is the file system 
under test.  To perform this test, run the following commands:

```bash
cd ~/Metis/fs-state/mcfs_scripts/
sudo ./single_ext2.sh
```

This script will clean up resources, create filesystem devices, and run Metis with 
Ext4 vs. Ext2.  Note that this experiment will be continuously running 
until it encounters a discrepancy (i.e., potential bug) between two file 
systems.  This experiment is only for demonstration purpose.  It will be unlikely 
to have a discrepancy between Ext4 and Ext2 in a short time, and waiting this experiment
till Metis ends will take weeks!  You can run `fs-state/stop.sh` to abort
the program half-way (which we highly recommend for this demo) or press Ctrl+C
to stop Metis (less recommended, as some resources are still not freed, e.g., mounted
file systems, devices).

In another shell session, do:

```bash 
cd ~/Metis/fs-state/
sudo ./stop.sh
```

After aborting Metis, you can see the logs saved under the `fs-state` folder to view 
the model-checking results and performance metrics. 
Metis logs serve as a critical role to identify, analyze and replay bugs.
While the model checker is running or terminated, the standard output is redirected to
`output-pan*.log` and the standard error is redirect to `error-pan*.log`. 
`output-pan*.log` records the timestamps, operations that have been performed, 
as well as the
arguments and results of each operation, and output abstract state. 
`error-pan*.log` logs the discrepancies
in behavior among the tested file systems that the model checker has
encountered. `error-pan*.log` is supposed to be empty if no discrepancy found.
There will also be a `sequence-pan-*.log` that records the 
sequence of file system
operations/arguments that have been performed by model checker in a easy-to-parse format.  

We have a log rotation mechanism to compress logs that are greater than 1GB and save 
them as `.log.gz` files to conserve disk space.
The sequence logs are intended for the replayer to replay operations and reproduce 
any potential bug. Performance metrics are logged in `perf-pan*.csv` files. The first 
column is the timestamp in seconds, and the second column is the number of file system operations 
performed, and the third column is the number of unique abstract states visited by Metis.
You can see format `number1-number2-number3` as the suffix of log filenames, where the number1 is 
timestamp for year, month, days, number2 is timestamp for hours, minutes, seconds, and number3 is
the pid of the Metis process (aka. `pan`).
If you want to delete all those logs,
you can run `sudo make clean` under the `fs-state` folder.

#### Set up RefFS 

We also created a new RefFS as Metis's reference file system.
Please refer to the [RefFS repository](https://github.com/sbu-fsl/RefFS) and its
[README](https://github.com/sbu-fsl/RefFS/blob/master/README.md) regarding the 
installation and mount of RefFS.  Before using RefFS, make sure RefFS is 
installed and can be mounted.

You can run RefFS vs. Ext4 by running the `single_verifs2.sh` script:

```bash
cd ~/Metis/fs-state/mcfs_scripts/
sudo ./single_verifs2.sh
```

Again, this experiment can take a very long time to complete (weeks or months), so 
you can abort it half-way via running `fs-state/stop.sh` or Ctrl+C.  The experimental
logs of RefFS vs. Ext4 should appear in the `fs-state` folder.  Also, the log file names show 
the timestamp and pid of the experiment, and you will see both file systems have the same abstract
state (MD5 hash) and returns/error codes after each operation. 

#### Using Metis replayer

After each experiment, we can use replayer to replay the exact sequence 
of operations to debug/reproduce the discrepancy/bug or obtain any intermediate 
file system state during a Metis run.  The Metis replayer parses the `sequence-pan*.log`
line by line, reads the operations/arguments, and performs the exact operations (including state save/restore)
on single or both file systems (specified by the replayer argument list).  
Let's use a previous Ext4 vs. Ext2 example to demonstrate Metis's replayer:

```bash
cd ~/Metis/fs-state/
sudo make clean # clear all previous logs and object files
cd ~/Metis/fs-state/mcfs_scripts/
sudo ./single_ext2.sh 
```

Then we abort the Metis process by Ctrl-C or running script `sudo ./stop.sh` after some time (10 minutes).
We recommend to use `stop.sh` because we also need to unmount all the 
file systems used by Metis.  Using Ctrl-C needs to manually unmount all 
the test file systems (i.e., `umount /mnt/test-*` or `umount /dev/ram*`).
After that, we can get a sequence log file and a dump_prepopulate log file
in the `fs-state` folder. 
We use `sequence-pan-20231214-014909-2031206.log` and `dump_prepopulate_0.log` as an example, 
and please replace the log file names with your own log files.  

We need to ensure that test devices are created with the correct device
types/sizes.  For Ext4 vs. Ext2, you can run `loadmods.sh` in the `fs-state`
to create desired ramdisks.
To use the replayer, we should first open the `fs-state/replay.c` file, 
edit **line 40 and line 46** to reflect the log file names generated 
from a previous experiment that we want to replay (esp. the sequence file name, `dump_prepopulate_0.log`
should be the same for every experiment).  Therefore, the 
replayer can use the correct log files to replay.  
After editing the `replay.c` file, we can compile the replayer by:

```bash 
cd ~/Metis/fs-state/
# Open and edit replay.c first (e.g., sudo vim replay.c)
# Make sure the log file names are correct and those files exist
# Compile the replayer everytime we change the replay.c file
sudo make replayer
# Load ramdisk devices for replaying Ext4 vs. Ext2
sudo ./loadmods.sh
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
Verification.  To support Swarm, we use a configuration file `fs-state/swarm.lib`
to specify necessary parameters (e.g., number of VTs).
You can find the detailed description
of the configuration file via the [Swarm README](https://github.com/sbu-fsl/swarm-mcfs/blob/swarm-v2/README.md).

To run a quick Metis experiment with Swarm for Ext4 vs. Ext2, please copy the 
`swarm-single-node.lib` to override `swarm.lib`, set up devices, run the `fs-state/setup_swarm.sh`
with proper arguments, and finally run the generated `mcfs-main.pml.swarm` script.

```bash
cd ~/Metis/fs-state/
# Use proper swarm.lib configuration file
yes | sudo sh -c 'cp -f swarm-single-node.lib swarm.lib'
# Clean up all previous logs and object files as running Metis with Swarm can produce many logs
sudo make clean
# Unmount file systems if rmmod brd failed
sudo umount /dev/ram*
# Remove all ramdisk devices
sudo rmmod brd
# Reload ramdisk devices for Ext4 vs. Ext2 with Swarm 
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

This section shows how to reproduce the experimental results in our paper.  We
provided scripts (in `Metis/ae-experiments`) and instructions to run experiments and collect data.
**Please let us know if you encounter any issues. We will response to you ASAP.**

#### Test Input Coverage (Figure 3, 4, 5)

Input coverage is a metric to measure the coverage of file system inputs (syscalls' arguments).
The arguments from file system syscalls are categorized into different types including identifiers,
bitmaps, numeric arguments, and categorical arguments.  We used different methods to partition
different types of file system test inputs.  Please refer to our paper for details.  

Metis can log its syscalls and arguments into `output` and `sequence` logs, but raw syscalls 
and arguments are not enough to compute input coverage.  We need to parse the logs to partition 
the inputs (syscalls and their arguments).  To achive this and support input coverage 
computation for a wide range of file system testing, we developed a tool called IOCov (see 
[our HotStorage '23 paper](https://www.fsl.cs.stonybrook.edu/docs/mcfs/iocov-hotstorage23.pdf) for details). 
IOCov can read and parse Metis logs and obtain input coverage just like we presented 
in this paper (Figure 3-5). To use IOCov and our scripts, **please put the `IOCov` folder and the `Metis` folder under the same directory.**  
For example, you can run the following commands to clone IOCov:

```bash
cd ~
# Metis should also be under the same directory
git clone git@github.com:sbu-fsl/IOCov.git
```

Therefore, the relative paths in our scripts can work.  Please install following Python packages
for IOCov:

```bash
sudo apt-get install python3-pip
# Don't forget the sudo before pip3 because all the scripts we run are under sudo
sudo pip3 install numpy scipy matplotlib
```

##### Figure 3 Input Coverage open flags 40 minutes

This experiment runs three different cases of Metis's input coverage for 
open flags: Metis-Uniform, Metis-RSD, and Metis-IRSD, as we showed in 
the Figure 3.  For each ease, we recompile Metis with different values 
of the marco `MY_OPEN_FLAG_PATTERN`, run Metis to test Ext4 only, 
abort Metis after 40 minutes, and call IOCov to compute input coverage of 
the Metis run based on its sequence log.
**Each case will take 40 minutes to complete, so this script will take about 2 hours to complete.**

```bash
cd ~/Metis/ae-experiments
sudo ./figure-3-exp.sh
```

After the script finishes, you can view the input coverage results in `~/IOCov/MCFS/`.
You should be able to see three `.pkl` files and three `.json` files.  Json files 
reflect the same content as pkl files but in a human-readable format.  
These three json files (sorted by timestamp or filename) are corresponding to the 
three cases of Metis's input coverage: Metis-Uniform, Metis-RSD, and Metis-IRSD.
You can read our paper to understand the definitions of these three cases.
For example, the oldest json file is for Metis-Uniform and the newest json file 
is for Metis-IRSD.
This is an example of my previous outputs (sorted by timestamp or filename):

```
~/IOCov/MCFS/input-cov-mcfs-20231223-031808-1471509.json --> Metis-Uniform
~/IOCov/MCFS/input-cov-mcfs-20231223-035811-1497210.json --> Metis-RSD
~/IOCov/MCFS/input-cov-mcfs-20231223-043814-1523714.json --> Metis-IRSD
```

You can view open json files and see the K-V pairs of `"open"` and `"flags"`.
The values should be matching with the Figure 3 in our paper.
Note that `O_ACCMODE` flag is not included in the figure, because this flag 
is set by two bits (`O_WRONLY` and `O_RDWR`) in the `open` syscall.  Therefore, you can 
ignore this flag in the json files.

Feel free to run `sudo ./cleanup-iocov.sh` to clean up all the IOCov logs if you 
don't want to have too many IOCov results.

##### Figure 4 Input Coverage write sizes 40 minutes

This experiment runs three different cases of Metis's input coverage for write sizes:
Metis-Uniform, Metis-XD, and Metis-IXD. The `write` sizes are the sizes of data to be written
from the buffer (i.e., the `count` argument in the [write](https://man7.org/linux/man-pages/man2/write.2.html) syscall).
Because there are too many values of write size can be used, we partition the input space 
of write sizes by the powers of 2 numbers (e.g., 1, 2, 4, 8, 16, etc.).  Please refer to our paper 
and our previous [HotStorage '23 paper](https://www.fsl.cs.stonybrook.edu/docs/mcfs/iocov-hotstorage23.pdf) for details.  

Similarly, the figure 4 experiment runs Metis to test Ext4 only, for 40 minutes. Each 
case uses a different value of the marco `MY_WRITE_SIZE_PATTERN` to recompile Metis.
**This script will take about 2 hours to complete.  Again, please make sure the required Python packages are properly installed, otherwise figures cannot be plotted.** 

```bash
cd ~/Metis/ae-experiments
sudo ./figure-4-exp.sh
```

Different from the Figure 3 experiment, this script not only produces json/pkl files but also creates figures
to show the input coverage distribution of each case.  The figures are saved in both `~/Metis/ae-experiments` and `~/IOCov/MCFS`.
You should be able to see following figures in PDF:

```bash
metis-write-size-Metis-Uniform-40m.pdf # Metis-Uniform
metis-write-size-Metis-XD-40m.pdf      # Metis-XD
metis-write-size-Metis-IXD-40m.pdf     # Metis-IXD
```

You can compare these figures to the figure 4 in the paper. Metis-Uniform indicates every partition of write size has 
the same probability to be chosen.  Metis-XD prioritizes testing smaller sizes more often, and Metis-IXD emphasizes the 
inverse: testing input partitions with larger write sizes.
Note that the input coverage in Metis is probabilistic, so 
you may not get the exact same figures as the paper (trend should be similar though). As the runtime of Metis increases,
the input coverage will be more accurate.
We show a 4-hour Metis experiment for write sizes of the same three cases in the next section, which should be 
more accurate than the 40-minute experiment, so you can see the distributions more clearly.

##### Figure 5 Input Coverage write sizes 4 hours

Figure 5 shows the input coverage of write sizes, each for a 4-hour Metis run.  This experiment is similar to 
the Figure 4 experiment, but with a different time length. **The script will last 12 hours to complete.**
Likewise, you can run the following commands to reproduce the Figure 5 experiment:

```bash
cd ~/Metis/ae-experiments
sudo ./figure-5-exp.sh
```

This script will produce three figures in PDF format:

```bash
metis-write-size-Metis-Uniform-240m.pdf # Metis-Uniform
metis-write-size-Metis-XD-240m.pdf      # Metis-XD
metis-write-size-Metis-IXD-240m.pdf     # Metis-IXD
```

You can compare these figures to the figure 5 in the paper.

#### Metis Performance and Scalability (Figure 6)


#### RefFS Performance and Reliability (Figure 7)

This experiment illustrates the performance of RefFS while running with Metis and its
comparison with other reference file systems including BtrFS, Ext2, Ext4, and XFS.
We created a script `figure-7-exp.sh` to run these five file systems with Metis for 10 minutes each.
**Therefore, this script will take about 1 hour to complete.** You can edit the `TIMERUN`variable
in the `figure-7-exp.sh` script to change to a longer or shorter time length for each file system.
The performance in the figure 7 is mesured by the number of file system operations and unique filesystem
abstract states per second. After each file system's Metis run, the script will read the performance
metrics from the `perf-pan*.csv` file and extract total number of operations and unique abstract states 
as well as epoch time in seconds.  Then, the script will compute the performance metrics and save them in the
`fig7_fs_perf_results` text file under the folder `~/Metis/fs-state/`.

You can view the performance results via the following command:

```bash
cd ~/Metis/fs-state/
cat fig7_fs_perf_results
```

#### Bug Finding

We listed the file system bugs found by Metis in the Table 2 of our paper. In `Metis/fs_bugs`, we provided
reproducers for some bugs. We use the reproducer for the #5 JFFS2 write_begin bug as an example.
We have explained the bug in Section 5.4 of the paper. For more information, please refer to the
[bug patch](https://github.com/torvalds/linux/commit/23892d383bee15b64f5463bd7195615734bb2415).
You can use the Ubuntu 20 machine (Metis-AE1-U20 instance) with a lower kernel version (i.e., Linux 5.4.0) to reproduce this JFFS2 write begin 
bug by either using our reproducer and Metis itself.

##### Reproduce the JFFS2 write_begin bug by the reproducer

Before running any JFFS2 experiments, please make sure you installed JFFS2 and MTD utilities by
the command below. We already installed them on the Metis-AE1-U20 instance.

```bash
sudo apt-get install mtd-utils
```

To run JFFS2 write_begin bug reproducer, please run the following commands to compile the simple C 
driver and run the shell script:

```bash
cd ~/Metis/fs_bugs/jffs2/write_begin/
make
sudo bash reproduce_jffs2_write_begin_issue.sh
```

You should be able to see the following output, which indicates the bug is reproduced:

```bash
the correct file should be 8 x 1s, then 12 x 0s, then 4 x 2s
the INcorrect file has 16 x 1s, then 4 x 0s, then 4 x 2s
00000000  01 01 01 01 01 01 01 01  01 01 01 01 01 01 01 01  |................|
00000010  00 00 00 00 02 02 02 02                           |........|
00000018
```

For the correct behavior, the file should have a hole that is zeroed out (i.e., 12 x 0s), but 
the reproducer shows the JFFS2 file system has 1s in the hole instead, indicating a
data corruption bug. 

##### Reproduce the JFFS2 write_begin bug by latest version of Metis

To run Metis to find this bug, we first need to edit line 26 of the `fs-state/parameters.py` file
to remove `0o40101` (`O_DIRECT`) from possible `open` flags because JFFS2 does not support this open flag. Otherwise, Metis will
abort with a discrepancy that JFFS2 returns an `EINVAL` error code.

We already changed this line on the Ubuntu 20.04 machine. If you use other machines, change this line in
`fs-state/parameters.py` from:

```python
create_open_flag = make_params_pml('create_open_flag',
        SpecialParameters(0o101, 0o301, 0o1101, 0o40101))
```

to 

```python
create_open_flag = make_params_pml('create_open_flag',
        SpecialParameters(0o101, 0o301, 0o1101))
```

Then, you can run Metis with Ext4 vs. JFFS2 where Ext4 serves as the reference file system and JFFS2 is the file system under test. We created a script `run-metis-jffs2.sh` to automate this process including cleaning up previous logs/devices, loading devices,
and running Metis. Please note that the current version of Metis involves randomization
in the file system operations (e.g., prepopulation of some files/dirs based on 
probability, selection of file/dir, etc.), so it may take varying time to detect the bug or report another JFFS2 bug. **But, it takes within 12 hours to detect this bug** based on our experience.  You can run the following commands to reproduce this bug:

```bash
# You should use the Ubuntu 20.04 machine or kernel version lower than or equal to v6.2
cd ~/Metis/ae-experiments/
sudo ./run-metis-jffs2.sh
```

Once the bug is detected, Metis will abort (no `pan` process running) and you can see the bug (discrepancy) report at `error-pan*.log` log files. The operations that lead to
the bug can be found at the bottom of the `output-pan*.log` log files. There will also 
be 20 file system images (10 images for each file system) dumped to help post-bug analysis and reproduction. You can mount these images to get the file system state close
to the bug. Filenames of these images show the state exploration depth and sequence ID
to better identify the file system state and the relationship with the bug.

##### Reproduce the JFFS2 write_begin bug more deterministically using older version Metis

There is an optional way to reproduce this bug more deterministically using an older version of Metis. We have cloned the older version of Metis in the `old-simpler-Metis/Metis` folder. This older version has already configured to test JFFS2 using Ext4 as
the reference, and **it can detect the JFFS2 bug in about 4 hours.** You can run the following commands to reproduce this bug:

```bash
cd ~/old-simpler-Metis/Metis/fs-state
# You may also want to clean up existing logs and devices
# make clean
# sudo rmmod mtdblock
# sudo rmmod mtdram 
# sudo rmmod mtd_blkdevs
# sudo rmmod brd

sudo ./loadmods.sh
sudo ./setup.sh
```

When Metis aborts, it indicates that the bug is detected. You can view 
the `error` and `output` logs in the `fs-state` folder for the 
information of the bug.
Note that the older version of Metis does not support dumped images after 
a potential bug is detected. 

##### Reproduce bugs from other file systems by Metis

Reproducing other bugs from other file systems is similar to the JFFS2 bug. 
You can use either run Metis itself or use our reproducer to detect/reproduce the bug. 
In `Metis/fs-states/mcfs_scripts`, we have provided a set of scripts to run Metis with different file systems (using Ext4 as the reference file system). You can edit the 
scripts easily to use RefFS or other file systems as a reference by changing 
the arguments provided to `./setup.sh -f` option. 
Because we have to use different `brd2` modules for different Linux kernel versions,
please make sure you use the correct version of brd2 module in `kernel` folder. For 
my information, please refer to [our document for brd2](kernel/brd/README.md).

In those scripts, by default we use:

```bash
cd ../kernel/brd-for-5.19.7
```

You need edit it accordingly based on your correct kernel version.  The default kernel 
version for Ubuntu 22.04 is 5.15.0 and Ubuntu 20.04 is 5.4.0. You need to edit this 
line to:

```bash
# For Ubuntu 22.04 default kernel version: 5.15.0
cd ../kernel/brd-for-5.15.0

# For Ubuntu 20.04 default kernel version: 5.4.0
cd ../kernel/brd
```

For example, you can test F2FS by running the following command (already changed
to 5.4.0 kernel version by using the brd2 module in the `Metis/kernel/brd` folder):

```bash
sudo rmmod brd
# Following command is optional, see Troubleshooting: Error message: ramdisk device issue
sudo rm /dev/ram*
cd ~/Metis/fs-state/mcfs_scripts
sudo ./single_f2fs.sh
```

As we discussed in the paper, some bugs are non-deteministic and may take a long time to detect (e.g., > 20 hours). Please feel free to use Swarm to accelerate the bug detection process.

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

## Citation 

```
@INPROCEEDINGS{fast24metis,
  TITLE =        "{Metis}: File System Model Checking via Versatile Input and State Exploration",
  AUTHOR =       "Yifei Liu and Manish Adkar and Gerard Holzmann and Geoff Kuenning and Pei Liu and Scott Smolka and Wei Su and Erez Zadok",
  NOTE =         "To appear",
  BOOKTITLE =    "Proceedings of the 22nd USENIX Conference on File and Storage Technologies (FAST '24)",
  ADDRESS =      "Santa Clara, CA",
  MONTH =        "February",
  YEAR =         "2024",
  PUBLISHER =    "USENIX Association"
}
```

```
@INPROCEEDINGS{hotstorage23iocov,
  TITLE =        "Input and Output Coverage Needed in File System Testing",
  AUTHOR =       "Yifei Liu and Gautam Ahuja and Geoff Kuenning and Scott Smolka and Erez Zadok",
  BOOKTITLE =    "Proceedings of the 15th ACM Workshop on Hot Topics in Storage and File Systems (HotStorage '23)",
  MONTH =        "July",
  YEAR =         "2023",
  PUBLISHER =    "ACM",
  ADDRESS =      "Boston, MA"
}
```

```
@INPROCEEDINGS{hotstorage21mcfs,
  TITLE =        "Model-Checking Support for File System Development",
  AUTHOR =       "Wei Su and Yifei Liu and Gomathi Ganesan and Gerard Holzmann and Scott Smolka and Erez Zadok and Geoff Kuenning",
  DOI =          "https://doi.org/10.1145/3465332.3470878",
  PAGES =        "103--110",
  BOOKTITLE =    "Proceedings of the 13th ACM Workshop on Hot Topics in Storage (HotStorage '21)",
  MONTH =        "July",
  YEAR =         "2021",
  PUBLISHER =    "ACM",
  ADDRESS =      "Virtual"
}
```

## Contact 
For any question, please feel free to contact Yifei Liu ([yifeliu@cs.stonybrook.edu](mailto:yifeliu@cs.stonybrook.edu))
and Erez Zadok ([ezk@cs.stonybrook.edu](mailto:ezk@cs.stonybrook.edu)).
