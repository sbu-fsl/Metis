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

### Distributed settings (Not perfect yet)

## How to evaluate?

## Limitations and issues
