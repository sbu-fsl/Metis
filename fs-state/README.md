# fs-state - Spin-based file system model checker

## Usage

### Prerequisites

#### Software

- [SPIN](http://spinroot.com/spin/whatispin.html) model checker

#### Kernel modules

- brd: RAM block device driver, see `kernel` folder in this repository
- mtdram: A kernel driver that simulates a
    [MTD device](http://www.linux-mtd.infradead.org/doc/general.html) using
    system RAM. Should have been shipped with your linux kernel
- mtdblock: A kernel driver that creates regular block devices based on
    MTD devices. Should have been shipped with your linux kernel.

#### Packages

- mtd-utils: Includes JFFS2 file system
- xfsprogs: XFS file system utilities
- libssl-dev: Required to calculate MD5 hash

### Preparations

#### 1. Test directory for each file system

Please create a test directory named `test-$fs` under `/mnt` for each file
system to be tested. `$fs` is the name of the file system.

For example, if you would like to test ext4 file system, then do the following:

```bash
$ sudo mkdir /mnt/test-ext4
```

#### 2. Load RAM block device driver

To speed up file system operations, the model checker uses RAM block devices as
the backend storage of the file systems to be tested. RAM block devices are even
much faster than files in tmpfs! You will need to load the RAM block device
driver (brd) using the following command:

```shell
$ sudo modprobe brd rd_size=$SIZE rd_nr=$N
```

`$SIZE` is the size of each RAM block device in kilobytes (default 4096).  `$N`
is the number of block devices generated (default 16). Note that no RAM will be
actually consumed until you write data into the block devices.

For ext2, ext4 file systems, please set the size to 256KB.

Other file systems require larger sizes. For example, xfs needs at least 16MB,
f2fs requires at least 40MB and btrfs requires at least 110MB.

jffs2 requires an MTD device, which will be discussed next.

You will need at least 2MB to enable the journaling in ext3 or ext4.

Note that the parameter `rd_size` applies to **all** RAM block devices it
creates.  That's a problem if you want to test file systems of different sizes.
The modified brd driver in `kernel` folder of this repository allows setting
sizes for individual block devices, so please compile and load that if you would
like to test file systems of varied sizes.

#### 3. Load mtdram driver for jffs2

jffs2 only works with
[MTD devices](http://www.linux-mtd.infradead.org/doc/general.html), which
represent raw unmanaged flash chips and are different from regular block devices.
Fortunately, there is a kernel module `mtdram` that can simulate a MTD device
via system RAM, and there is a module `mtdblock` that emulates block devices
over MTD devices. By using the two modules, we can have the JFFS2 file system
work without a physical MTD hardware. To set up such a device, load the modules
using the following commands:

```shell
$ sudo modprobe mtd 
$ sudo modprobe mtdram total_size=256 erase_size=16
$ sudo modprobe mtdblock
```

`total_size` is the size of the RAM-simulated MTD device in kilobytes.
`erase_size` is the size of a erase block, also in kilobytes.

After successfully executing the commands, you should see a block device called
`mtdblock0` in `/dev` directory.

#### 4. Create the JFFS2 file system.

Generally you don't need this step because the setup script handles this for
you. However you will need to set up file systems manually if you would like
to run the model checker via `make`. Setting up ordinary file systems, such as
ext2, ext4 and xfs, can be as simple as `mkfs` and `mount`, but JFFS2 is quite
different as there are extra steps:

First, create a empty directory:

```bash
$ mkdir /tmp/_empty
```

Then, create the JFFS2 file system image using the empty directory as the root
and pad the image to the desired size (256KB):

```bash
$ mkfs.jffs2 --root=/tmp/_empty --pad=262144 -o /tmp/jffs2.img
```

Next, "burn" the image into the RAM-backed MTD block device:

```bash
$ sudo dd if=/tmp/jffs2.img of=/dev/mtdblock0 bs=16k
```

Finally, you should be able to mount the file system:

```bash
$ sudo mount -t jffs2 -o rw,sync,noatime /dev/mtdblock0 /mnt/test-jffs2
```

### Run with automatic setup script

The easiest way to run the file system model checker is to use the automatic
setup script with the following command:

```bash
sudo ./setup.sh
```

The setup script provides the following options:

- `--abort-on-discrepancy, -a`: Abort the model checker whenever it encounters
  a behavior discrepancy among the tested file systems.
- `--keep-fs, -k`: Do not unmount the tested file systems when the model checker
  exits. This is useful for debugging.
- `--verbose, -v`: Be more verbose.

This script will create a JFFS2 file system on /dev/mtdblock0 and a XFS file
system on /dev/ram0. The model checker assumes that the size of /dev/mtdblock0
is 256KB and that of /dev/ram0 is 16MB. It is recommended that you have no less
than 64GB of physical RAM to run this model checker, or you need to create have
a large enough swap space. Otherwise the model checker will fail midway with
out-of-memory error. Later we will discuss how to modify the script and the
model checker to test other file systems.

As the model checker is running, the standard output is redirected to
`output.log` and the standard error is redirect to `error.log`. `output.log`
records the timestamps, operations that have been performed, as well as the
parameters and results of each operation. `error.log` logs the discrepancies
in behavior among the tested file systems that the model checker has
encountered. The model checker will also log the current f/s operations per
second every 10 seconds into `error.log`.

There will also be a `sequence.log` that records the sequence of file system
operations that have been performed by model checker in a easy-to-parse format.
This is intended for the replayer to use.

The setup script will fork a child shell process that monitors the memory usage
of the model checker process (`./pan`). The monitor generates `pan_mem_stat.csv`
in the following format:

```
epoch_secs,pid,proc_name,proc_state,phys_mem_in_pages
```

For the meaning of `proc_state`, see `man proc` and search for
`/proc/[pid]/stat`.

You can wait till the model checker ends or press Ctrl+C to abort the program
half-way. When the model checker exits, the ownership of all resources
(including logs, generated C code and compiled binaries) will be given back
to the login user.

### Using Makefile

It is not recommended to run the model checker via Makefile because you will
have to set up the file systems manually, and you can't test other file systems
by solely using `make`. However, there is an option doing so, provided that you
have set up the RAM-backed block devices, formatted and mounted the file
systems.

```bash
sudo make run
```

This will compile and execute the model checker. All outputs will printed to
the terminal, and there won't be the memory usage monitor as it's a component
in the setup script. The generated files will remain owned by root.

#### Other make rules

- `make clean`: Clean up executables, logs and generated code (`pan.*`)
- `make abstractfs-test`: Compile the demo program that computes the "abstract
    file system state" of a directory or a file system
- `make replayer`: Compile the file system operations sequence replayer

## Testing other file systems.

You will need to modify the setup script (`setup.sh`) and the model checker
code (`demo.pml`) in order to have the model checker test other file systems.
Here are the parts that need to be modified:

#### 1. Setup Script (`setup.sh`)

First, you need to modify the two variables: `FSLIST` and `DEVLIST`, which are
arrays that list the name of file systems to be tested and their corresponding
paths to devices serving as the underlying storage.

Only JFFS2 requires `/dev/mtdblock0` device, and it's highly recommended that
you use `/dev/ramN` (where N is in the range of 0 and `rd_nr-1`) as the storage
device for other file systems.

Each file system should have the corresponding setup and unset functions in the
script called `setup_$fs()` and `unset_$fs()` respectively. If you would like to
test ext2(256K), ext4(256K), jffs2(256K) or xfs(16M) file systems, that's all
you need to do with the setup script because their setup and unset functions are
already provided. If you want different sizes then you'll need to modify these
setup functions (e.g. you need at least 2MB to enable journaling in ext4).

If you would like to test other file systems whose setup and unset functions are
not present, you will need to write them on your own. The setup function should
create a clean file system that is ready to be mounted, and the unset function
should clean up any states that could prevent setting up next time. Instead of
hardcoding the device where the file system stores, the function should accept
an argument as the path to the device.

Normally setting up a file system just involves zeroing the device using `dd`
and formatting the device with `mkfs.$fs`. You don't need to set up loop devices
(which is not recommended) since you are already working with a block device
(`/dev/ramN`). Also you don't need to mount the file system in the setup
function. For unset functions, it's usually empty for most file systems. If the
file system you would like to test is special and needs extra steps like JFFS2,
you need to be careful. Do not use `sudo` because the user of the script will
use it. Use `runcmd` wrapper when invoking a command so that the script will
perform cleanups and stop running further if the command failed.

As an example, if you would like to test ext4 and nilfs2 file systems, then you
should modify the script in the following way:

```bash
# Replace FSLIST and DEVLIST
FSLIST=(ext4 nilfs2)
DEVLIST=(/dev/ram0 /dev/ram1)

# Add setup and unset functions for nilfs2
setup_nilfs2() {
    DEVFILE=$1
    BLOCKSIZE=1k
    COUNT=2048
    runcmd dd if=/dev/zero of=$DEVFILE bs=$BLOCKSIZE count=$COUNT status=none
    runcmd mkfs.nilfs2 -B 16 $DEVFILE
}

unset_nilfs2() {
    :
}
```

#### 2. The model checker code (`demo.pml`)

To begin with, you will need to change the elements in the array `fslist[]` to
the names of the file systems you want to test (in line 6). Besides, you need to
declare a pointer `void *fsimg_$fs` and a integer variable `int fsfd_$fs` for
each file system you would like to test inside this `c_decl` block. `$fs` is
the name of the file system.

Then, you should have the model checker track the images of the file systems
(or rather, the full content of the block devices which the file systems are
built on). This is done by removing the existing `c_track` statements that
tracks the images of jffs2 and xfs, and add your own `c_track` statements
that look like this:

```promela
c_track "fsimg_$fs" "$size" "UnMatched"
```

`fsimg_$fs` is the `void *` pointer you decleared in the previous step.
`$size` is the size of the block device in bytes. `"UnMatched"` means that the
image will only be used as concrete states for restoration, not abstract states
for matching. The model checker uses a special utility function to calculate the
abstract file system states on its own.

The `void *` pointers should be initialized in `proctype driver()` via `mmap()`
syscall. In the embedded C code block of this proctype, you need to open the
block devices in read-write mode (`O_RDWR`) and then memory-map them. Assign
the pointers with the addresses returned by `mmap()`. For example, if you want
to model check ext2 and ext4, then the code should be as follows:

```c
fsfd_ext2 = open("/dev/ram0", O_RDWR);
assert(fdfd_ext2 >= 0);
fsimg_ext2 = mmap(NULL, fsize(fsfd_ext2), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext2, 0);
assert(fsimg_ext2 != MAP_FAILED);

fsfd_ext4 = open("/dev/ram1", O_RDWR);
assert(fdfd_ext4 >= 0);
fsimg_ext4 = mmap(NULL, fsize(fsfd_ext4), PROT_READ | PROT_WRITE, MAP_SHARED, fsfd_ext4, 0);
assert(fsimg_ext4 != MAP_FAILED);
```

`fsize()` is a helper function that retrieves the size of an opened file or
block device. Don't forget to comment out or remove the old code that does the
same thing!

#### 3. Save your modification

After the modification you can run `sudo ./setup.sh` to model check the file
systems you want. It is highly recommended that you commit your changes into a
new branch.

## Discussions

### Abstract file system states

### Size of file systems

## Other components

### Replayer

### Auto replayer script

### Abstract file system states demo
