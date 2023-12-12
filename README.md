# Metis: File System Model Checking via Versatile Input and State Exploration

This is the artifact for the FAST '24 paper **"Metis: File System Model Checking 
via Versatile Input and State Exploration"**.  Metis is a
model-checking framework designed for versatile, thorough, yet
configurable file system testing in the form of input and state
exploration.

Metis was formerly known as MCFS (Model Checking File System).

## Setup Metis and RefFS with model checking environment 

We tested Metis on Ubuntu 22.04 and Ubuntu 20.04 with Linux kernel versions 
specified in `./kernel` (i.e., 4.4, 4.15, 5.4, 5.15.0, 5.19.7, 6.0.6, 6.2.12, 6.3.0, and 6.6.1).  We cannot guarantee the functionality and usability on other 
Ubuntu or Linux kernel versions.  Metis is built on the top of the SPIN 
model checker and Swarm Verification.  Metis relies on a reference file 
system to check a file system under test, and we use RefFS or Ext4 as 
the reference file system.  Other file systems can also serve as the 
reference file systems.

***Other repositories/artifacts along with Metis***

RefFS: https://github.com/sbu-fsl/fuse-cpp-ramfs
fsl-spin (modified version of SPIN): https://github.com/sbu-fsl/fsl-spin 
swarm-mcfs (modified version of Swarm): https://github.com/sbu-fsl/swarm-mcfs

Note that we must use `fsl-spin` for the SPIN model checker for Metis 
and `swarm-mcfs` for the Swarm Verification tool, and the vanilla SPIN/Swarm
cannot work with Metis.

Please check out each repository for respective documentation.

## Artifact Eval: Machines 

We have provided VMs for each AEC member.  TODO

## Artifact Eval: System Configuration and Test Run 

We have configured the necessary environments on the machines provided 
to AEC members, so you don't need to set up environment by yourself.  
If you really want to set up Metis on your own machine,
You can use our `setup-deps.sh` bootstrap script.

```bash 
cd scripts
sudo ./setup-deps.sh
```

### Simple Metis run to check Ext2 with Ext4





### Set up RefFS 


## Artifact Eval: Reproduction of Experimental Results



## Major Components:

This repo consists of multiple folders.  Below are concise descriptions 
of each folder.

### driver-fs-state




### fs-state

The Spin-based file system model checker we are currently developing.
This checker will run a set of file system operations (system calls)
non-deterministically on multiple file systems, and then compare their
behavior. If there's any discrepancy, the checker will log it.

Please enter the folder to see detailed document and code.

### fs_bugs


### kernel

Kernel modules that helps the file system model checker

### scripts

### other folders

## Reference 

## Contact 
For any question, please feel free to contact Yifei Liu ([yifeliu@cs.stonybrook.edu](mailto:yifeliu@cs.stonybrook.edu))
and Erez Zadok ([ezk@cs.stonybrook.edu](mailto:ezk@cs.stonybrook.edu)).
