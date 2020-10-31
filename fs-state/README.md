# fs-state - Spin-based file system model checker

## Table of Content

- [fs-state - Spin-based file system model checker](#fs-state---spin-based-file-system-model-checker)
  * [Usage](#usage)
    + [Prerequisites](#prerequisites)
      - [Software](#software)
      - [Kernel modules](#kernel-modules)
      - [Packages](#packages)
    + [Preparations](#preparations)
      - [1. Test directory for each file system](#1-test-directory-for-each-file-system)
      - [2. Load RAM block device driver](#2-load-ram-block-device-driver)
      - [3. Load mtdram driver for jffs2](#3-load-mtdram-driver-for-jffs2)
      - [4. Create the JFFS2 file system.](#4-create-the-jffs2-file-system)
    + [Run with automatic setup script](#run-with-automatic-setup-script)
    + [Using Makefile](#using-makefile)
      - [Other make rules](#other-make-rules)
  * [Testing other file systems.](#testing-other-file-systems)
      - [1. Setup Script (`setup.sh`)](#1-setup-script-setupsh)
      - [2. The model checker code (`demo.pml`)](#2-the-model-checker-code-demopml)
      - [3. Save your modification](#3-save-your-modification)
  * [Discussions](#discussions)
    + [Abstract file system states](#abstract-file-system-states)
      - [Background](#background)
      - [Design](#design)
      - [Implementation](#implementation)
      - [Demo](#demo)
    + [Size of file systems](#size-of-file-systems)
    + [RAM block devices or image files on tmpfs?](#ram-block-devices-or-image-files-on-tmpfs)
    + [States of the file systems being tracked](#states-of-the-file-systems-being-tracked)
  * [Other components](#other-components)
    + [Replayer](#replayer)
    + [Auto replayer script](#auto-replayer-script)

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

#### Background

In the area of model checking, there are two concepts: abstract states and
concrete states. Both of them describe the system being checked, but they are
used in different ways. After each step (called "transition") of the model
checking process being taken, the model checker collects the abstract and
concrete states of the system. The abstract state can be regarded as a signature
identifying different system states. If after a transition the abstract state
matches one stored in previous exploration, the model checker will recognize
that this state already been visited. In this case, the model checker will
restore the system state to the parent of the exploration tree using the
concrete state. The concrete states serve as snapshots of system states that
have been explored.

Therefore, the concrete states should contain all the information that describes
the states of the system being checked, usually the local and global variables.
The abstract state can be the same as the concrete state because the concrete
state has all the information to describe a state and distinguish different
states. By default this is what Spin does. However, this approach of using the
full concrete state as the abstract state is not ideal, not only because
comparing a large number of bytes is inefficient, but also because the full
concrete state may contain some "noisy" properties that we are not interested in
and should not be taken into consideration when comparing logical equivalency
between states.

An example is that two instances of file systems should be considered the same
as long as the directory tree, the content of the files and the key metadata of
the files (such as file type, ownership and size) in the two instances are the
same, regardless of the timestamps, the order of files under a directory or the
position of inodes on the physical storage. In this case, two logically
equivalent file system instances may have different raw disk images due to those
"noisy", uninterested properties in the raw storage. Therefore, it is no longer
proper to directly use the raw disk or ramdisk images as the abstract states. If
we use the raw images as the abstract states, the model checker will explore
more states and consume much more memory, causing "state explosion", even though
a lot of of these states are actually equal logically. Worse, the state
exploration may never converge because the timestamps will always change to
different values every time a mutating file system operation is performed.

Thus, we would like to design our own abstract states that describe the logical
states of the file systems. The custom abstract state will be much smaller than
the raw file system images and contain only properties of interest, omitting
those "noisy" properties.

#### Design

In our Spin-based file system model checker, the abstract file system states are
abstract states that describe the logical states of the file systems being
tested. For each file system, the abstract file system state is a 128-bit MD5
hash value computed by collecting data in the following steps:

1. Start from the mounting point of the file system as the root directory.
2. For each directory, call `readdir()` to retrieve all children entries under
   this directory.
3. Sort the entries in lexicology order. This step ensures that lists of the
   same set of files are always identical and the chronological order of file
   creations won't matter.
4. For each entry, `stat()` the file and collect the key attributes: uid, gid,
   mode, size, number of links. Ignore size and nlinks if the current entry is
   not a regular file. Feed these attributes into the MD5 hasher. Also feed the
   absolute path to this entry into the MD5 hasher. The path to the mounting
   point is contracted into root (`/`).
5. If the entry is a file, feed the file content into the MD5 hasher.
6. If the entry is a directory, repeat step 2 recursively.
7. Return the final MD5 hash when the entry iteration is finished.

If there are N file systems to be tested, there will be N 128-bit MD5 hashes.
Thus, Spin will do `c_track` on an array of N 128-bit hash values.

`size` is ignored for non-regular files because different file systems have
different behavior in reporting sizes for directories. The `nlinks` attribute
is also ignored for directories because the JFFS2's root directory has 3 links,
which is different from any other file systems we experimented with.

#### Implementation

The detailed implementation of abstract state generation is in `abstract_fs.cpp`
and `abstract_fs.h`. The header defines the following data structures:

```c
typedef unsigned char absfs_state_t[16];

struct abstract_fs {
  MD5_CTX ctx;
  absfs_state_t state;
};

typedef struct abstract_fs absfs_t;
```

`absfs_state_t` is a 128-bit buffer where the MD5 hash stores. The abstract file
system object `absfs_t` contains an MD5 hasher context `ctx` and a hash result
buffer `state`.

There are four APIs exposed to users and they are callable in C programs:

```c
/* Initialize the abstract file system object */
void init_abstract_fs(absfs_t *absfs);
/* Walk the directory tree starting from `basepath` and get the hash value.
 * If verbose is set to true, this function will log messages into verbose_outf
 * every time it iterates a file entry */
int scan_abstract_fs(absfs_t *absfs, const char *basepath, bool verbose,
                     FILE *verbose_outf);
/* Print the hex format of the hash value into the FILE object `out` */
void print_abstract_fs_state(FILE *out, absfs_state_t state);
/* Interpret the file mode in human readable form and write into
 * the FILE object `out`. */
void print_filemode(FILE *out, mode_t mode);
```

In the main model checker code, the abstract file system states are declared in
the following form:

```c
absfs_state_t absfs[n_fs];
```

where `n_fs` is the number of file systems hardcoded in the array `fslist[]`.
The array is tracked by this `c_track` statement:

```promela
c_track "absfs" "sizeof(absfs)";
```

The file system images (aka. persistent states, or the content of the ramdisks)
are `c_track`'ed in unmatched mode so that they will be regarded as concrete
states:

```promela
c_track "fsimg_jffs2" "262144" "UnMatched";
c_track "fsimg_xfs" "16777216" "UnMatched";
```

After calling each file system operation, the abstract file system state of the
file system being operated on will be updated via the aforementioned APIs. The
model checker will recognize the update and try to check if the state is visited
before.

#### Demo

To have a more intuitive view of the abstract file system state, you can compile
the demo program using `make abstractfs-test` and then run `./absfs` on an
directory. For example:

```bash
$ make abstractfs-test
$ sudo ./absfs /usr/local/include 2>&1 > absfs.log
$ less absfs.log
```

In the output, you will see something like this:

```
Iterating directory '/usr/local/include'...
/, mode=<dir 755>, size=4096 (Ignored), nlink=8, uid=0, gid=0
/benchmark, mode=<dir 755>, size=4096 (Ignored), nlink=2, uid=0, gid=0
/benchmark/benchmark.h, mode=<file 644>, size=54678, nlink=1, uid=0, gid=0
/benchmark/benchmark_api.h, mode=<file 644>, size=30805, nlink=1, uid=0, gid=0
/benchmark/macros.h, mode=<file 644>, size=2181, nlink=1, uid=0, gid=0
/benchmark/reporter.h, mode=<file 644>, size=6704, nlink=1, uid=0, gid=0
/fmt, mode=<dir 755>, size=4096 (Ignored), nlink=2, uid=0, gid=0
/fmt/chrono.h, mode=<file 644>, size=35368, nlink=1, uid=0, gid=0
/fmt/color.h, mode=<file 644>, size=22436, nlink=1, uid=0, gid=0
/fmt/compile.h, mode=<file 644>, size=19830, nlink=1, uid=0, gid=0kkkj
......
/ntirpc/version.h, mode=<file 644>, size=385, nlink=1, uid=0, gid=0
Iteration complete. Abstract FS signature = 268066d56a4444c3bacdb2cd04ab6bad
```

### Size of file systems

When testing the file systems, we would like to create ramdisks that are as
small as possible, because we want to allow the model checker to explore more
number of states with the same amount of memory (the model checker will save a
full copy of the ramdisk in memory for each distinct file system state!), and we
would like to have the file systems reach corner cases (such as `ENOSPC`) more
quickly.

Different file systems may require different minimum sizes. For example, ext4,
ext2 and jffs2 can utilize small disks as little as 256KB, whereas xfs requires
16MB and btrfs requires 110MB. Also to enable journaling on ext4 you need at
least 2MB.

An issue with the original ramdisk driver is that one size parameter `rd_size`
applies to all block devices it creates. Fortunately, I provided a modified
ramdisk driver that supports individualized sizes. For more information, please
see `kernel/brd` in this repository.

### RAM block devices or image files on tmpfs?

Disks are slow. Even for high end NVMe drives, the random I/O speed is still
much slower than DRAM. Therefore we want to use RAM as the backend storage of
the file systems being tested. There are actually two ways of utilizing RAM: one
is to create image files on tmpfs and then mount the images via loopback
devices, and the other is to use RAM block devices created by the `brd` kernel
driver module.

It seems that both options are OK, but in reality they aren't --- image files on
tmpfs + loopback devices is MUCH slower than RAM block devices. Here are the
experiments:

```bash
# Setup
sudo modprobe brd rd_nr=1 rd_size=3000000
dd if=/dev/zero of=/tmp/ext4.img bs=1M count=3000
sudo mkfs.ext4 /dev/ram0
LOOPDEV=$(sudo losetup -f --show /tmp/ext4.img)
sudo mkfs.ext4 $LOOPDEV
sudo mkdir /mnt/ramdisk-ext4
sudo mount -t ext4 /dev/ram0 /mnt/ramdisk-ext4
sudo mkdir /mnt/tmpfs-ext4
sudo mount -t ext4 $LOOPDEV /mnt/tmpfs-ext4
```

fio test of the ext4 file system over tmpfs:

```
$ sudo fio --directory=/mnt/tmpfs-ext4 --name=test --ioengine=libaio --iodepth=1 --rw=randrw --bs=4k --direct=1 --size=2500M --numjobs=1 --runtime=60 --loops=10

test: (g=0): rw=randrw, bs=(R) 4096B-4096B, (W) 4096B-4096B, (T) 4096B-4096B, ioengine=mmap, iodepth=1
fio-3.16
Starting 1 process
test: Laying out IO file (1 file / 2500MiB)
Jobs: 1 (f=1): [m(1)][98.4%][r=5392KiB/s,w=5284KiB/s][r=1348,w=1321 IOPS][eta 00m:01s]
test: (groupid=0, jobs=1): err= 0: pid=507810: Sat Oct 31 01:08:41 2020
  read: IOPS=1657, BW=6630KiB/s (6789kB/s)(388MiB/60001msec)
    clat (usec): min=97, max=24302, avg=234.84, stdev=139.64
     lat (usec): min=97, max=24303, avg=235.30, stdev=139.74
    clat percentiles (usec):
     |  1.00th=[  125],  5.00th=[  133], 10.00th=[  143], 20.00th=[  161],
     | 30.00th=[  172], 40.00th=[  188], 50.00th=[  208], 60.00th=[  231],
     | 70.00th=[  262], 80.00th=[  297], 90.00th=[  359], 95.00th=[  412],
     | 99.00th=[  553], 99.50th=[  644], 99.90th=[ 1057], 99.95th=[ 1582],
     | 99.99th=[ 3589]
   bw (  KiB/s): min= 4008, max=10752, per=100.00%, avg=6635.87, stdev=1494.76, samples=119
   iops        : min= 1002, max= 2688, avg=1658.95, stdev=373.68, samples=119
  write: IOPS=1656, BW=6625KiB/s (6784kB/s)(388MiB/60001msec); 0 zone resets
    clat (usec): min=172, max=9224, avg=355.70, stdev=160.46
     lat (usec): min=172, max=9225, avg=356.35, stdev=160.65
    clat percentiles (usec):
     |  1.00th=[  190],  5.00th=[  202], 10.00th=[  219], 20.00th=[  245],
     | 30.00th=[  265], 40.00th=[  289], 50.00th=[  322], 60.00th=[  355],
     | 70.00th=[  396], 80.00th=[  449], 90.00th=[  537], 95.00th=[  611],
     | 99.00th=[  799], 99.50th=[  922], 99.90th=[ 1631], 99.95th=[ 2147],
     | 99.99th=[ 4490]
   bw (  KiB/s): min= 3960, max=10552, per=100.00%, avg=6625.19, stdev=1471.53, samples=119
   iops        : min=  990, max= 2638, avg=1656.28, stdev=367.86, samples=119
  lat (usec)   : 100=0.01%, 250=44.94%, 500=47.52%, 750=6.67%, 1000=0.64%
  lat (msec)   : 2=0.18%, 4=0.03%, 10=0.01%, 50=0.01%
  cpu          : usr=6.35%, sys=27.37%, ctx=695156, majf=198834, minf=107
  IO depths    : 1=100.0%, 2=0.0%, 4=0.0%, 8=0.0%, 16=0.0%, 32=0.0%, >=64=0.0%
     submit    : 0=0.0%, 4=100.0%, 8=0.0%, 16=0.0%, 32=0.0%, 64=0.0%, >=64=0.0%
     complete  : 0=0.0%, 4=100.0%, 8=0.0%, 16=0.0%, 32=0.0%, 64=0.0%, >=64=0.0%
     issued rwts: total=99452,99382,0,0 short=0,0,0,0 dropped=0,0,0,0
     latency   : target=0, window=0, percentile=100.00%, depth=1

Run status group 0 (all jobs):
   READ: bw=6630KiB/s (6789kB/s), 6630KiB/s-6630KiB/s (6789kB/s-6789kB/s), io=388MiB (407MB), run=60001-60001msec
  WRITE: bw=6625KiB/s (6784kB/s), 6625KiB/s-6625KiB/s (6784kB/s-6784kB/s), io=388MiB (407MB), run=60001-60001msec

Disk stats (read/write):
  loop2: ios=198241/297330, merge=0/0, ticks=19320/25233, in_queue=36, util=99.78%

```

ext4 over ramdisk:

```
$ sudo fio --directory=/mnt/ramdisk-ext4 --name=test --ioengine=mmap --iodepth=1 --rw=randrw --bs=4k --direct=1 --size=2500M --numjobs=1 --runtime=60 --loops=10

test: (g=0): rw=randrw, bs=(R) 4096B-4096B, (W) 4096B-4096B, (T) 4096B-4096B, ioengine=mmap, iodepth=1
fio-3.16
Starting 1 process
test: Laying out IO file (1 file / 2500MiB)
Jobs: 1 (f=1): [m(1)][100.0%][r=167MiB/s,w=168MiB/s][r=42.8k,w=42.9k IOPS][eta 00m:00s]
test: (groupid=0, jobs=1): err= 0: pid=508496: Sat Oct 31 01:12:17 2020
  read: IOPS=39.5k, BW=154MiB/s (162MB/s)(9252MiB/60000msec)
    clat (usec): min=2, max=33549, avg= 5.55, stdev=33.23
     lat (usec): min=2, max=33549, avg= 5.63, stdev=33.23
    clat percentiles (nsec):
     |  1.00th=[ 2864],  5.00th=[ 2960], 10.00th=[ 3024], 20.00th=[ 3120],
     | 30.00th=[ 3184], 40.00th=[ 3280], 50.00th=[ 3440], 60.00th=[ 4384],
     | 70.00th=[ 5088], 80.00th=[ 7840], 90.00th=[11328], 95.00th=[12480],
     | 99.00th=[17024], 99.50th=[20352], 99.90th=[30336], 99.95th=[38144],
     | 99.99th=[82432]
   bw (  KiB/s): min=54688, max=192008, per=99.77%, avg=157527.95, stdev=30682.76, samples=119
   iops        : min=13672, max=48002, avg=39381.98, stdev=7670.68, samples=119
  write: IOPS=39.5k, BW=154MiB/s (162MB/s)(9247MiB/60000msec); 0 zone resets
    clat (usec): min=10, max=33490, avg=16.63, stdev=39.13
     lat (usec): min=11, max=33490, avg=16.77, stdev=39.44
    clat percentiles (usec):
     |  1.00th=[   13],  5.00th=[   14], 10.00th=[   15], 20.00th=[   15],
     | 30.00th=[   16], 40.00th=[   16], 50.00th=[   16], 60.00th=[   17],
     | 70.00th=[   17], 80.00th=[   18], 90.00th=[   19], 95.00th=[   21],
     | 99.00th=[   29], 99.50th=[   33], 99.90th=[   56], 99.95th=[   67],
     | 99.99th=[  241]
   bw (  KiB/s): min=55560, max=195440, per=99.76%, avg=157426.24, stdev=30724.25, samples=119
   iops        : min=13890, max=48860, avg=39356.54, stdev=7681.05, samples=119
  lat (usec)   : 4=29.44%, 10=13.72%, 20=53.69%, 50=3.07%, 100=0.06%
  lat (usec)   : 250=0.01%, 500=0.01%, 750=0.01%, 1000=0.01%
  lat (msec)   : 2=0.01%, 4=0.01%, 10=0.01%, 20=0.01%, 50=0.01%
  cpu          : usr=32.40%, sys=67.55%, ctx=235, majf=640000, minf=2968263
  IO depths    : 1=100.0%, 2=0.0%, 4=0.0%, 8=0.0%, 16=0.0%, 32=0.0%, >=64=0.0%
     submit    : 0=0.0%, 4=100.0%, 8=0.0%, 16=0.0%, 32=0.0%, 64=0.0%, >=64=0.0%
     complete  : 0=0.0%, 4=100.0%, 8=0.0%, 16=0.0%, 32=0.0%, 64=0.0%, >=64=0.0%
     issued rwts: total=2368477,2367160,0,0 short=0,0,0,0 dropped=0,0,0,0
     latency   : target=0, window=0, percentile=100.00%, depth=1

Run status group 0 (all jobs):
   READ: bw=154MiB/s (162MB/s), 154MiB/s-154MiB/s (162MB/s-162MB/s), io=9252MiB (9701MB), run=60000-60000msec
  WRITE: bw=154MiB/s (162MB/s), 154MiB/s-154MiB/s (162MB/s-162MB/s), io=9247MiB (9696MB), run=60000-60000msec

Disk stats (read/write):
  ram0: ios=0/0, merge=0/0, ticks=0/0, in_queue=0, util=0.00%
```

From the test results we can see that the RAM block device can be faster than
tmpfs images by two orders of magnitude. Therefore, we really should use
ramdisks instead of tmpfs files.

### States of the file systems being tracked

Ideally, the model checker should be able to track **all** information
related to the system being tracked. This might be quite easy and natural for
CPS (cyber-physical system) applications and embedded file systems because there
is no such things as "kernel" in those systems. However, this is not trivially
possible for file systems running on regular operating systems, because they run
in the kernel space of the operating system, and the model checker as a
user-space application has no access to the kernel memory. Therefore, the
Spin-based file system model checker cannot track the in-memory states of those
file systems.

FUSE allows us to develop file systems that run in user space, but the Spin
model checker cannot track full in-memory states of FUSE-based file systems
either for two reasons:

- First, those FUSE-based file systems run as an independent process, and there
  is no straightforward way for the model checker to track and restore all
  mutable memory segments of an independent process. We tried to modify the
  `morecore` interface in glibc's malloc library to delegate the FUSE-based file
  system's heap to a shared memory object which the model checker can mmap,
  track and restore. But then we found that only tracking & restoring the heap
  will cause inconsistencies between the heap and other memory segments of the
  process (such as data and bss segments where global and static variables
  locate), thus crashing the file system process.

- Second, FUSE based file systems also have some information maintained by the
  kernel, such as opened files and mounting status.

Besides, the availability of stable and well-maintained FUSE-based file systems
is extremely limited --- most of these user-space file systems are toys or
course projects that contain a lot of bugs and are likely to be incomplete. Very
few popular in-kernel file systems have been ported to FUSE. One may port a
in-kernel file system, such as xfs and btrfs, to FUSE, but there is no guarantee
for bug-free or preseverance of original behavior.

Therefore, at this moment we decide to track only persistent states (i.e.
ramdisks or file system images) of the file systems being tested. We will
attempt to address the challenge of tracking full states of in-kernel file
systems later. Most of the file systems we model checked using this approach did
not crash, but ext2/ext4 did manifest file system corruption bugs and we are
investigating it.

Furthermore, in the proposal we plan to use ramfs/tmpfs as the "reference file
system" by virtue of its simplicity and compliance with POSIX. This is not
feasible at this moment because all file data and metadata is located in the
kernel memory.

## Other components

### Replayer

The replayer replays the file system operations executed by the Spin mode
checker recorded in `sequence.log`. The purpose of this replayer is to replicate
the file system corruption bugs in ext2/ext4 we discussed in the meetings.

This replayer will do the following:

- Initialize a clean ext4 file system on a ramdisk and mount it on
    `/mnt/test-ext4`. See `void init()` in the code
- Parse `sequence.log` line by line, and execute the file system operation with
    given arguments.
- After each execution, check if the file system is in good state by testing the
    two bugs we discussed (See `bool fs_is_good()`).
- After each execution, the there's a probability (`prob_ckpt`) that the file
    system is checkpointed by taking a full snapshot of the ramdisk, and there
    is a probability (`prob_rest`) that the file system is restored to an
    earlier snapshot by writing the ramdisk with the saved snapshot (on
    condition that there is one). This step emulates what Spin does in state
    restoration. (See `ckpt_or_restore` func.)

Before running the replayer, please open `sequence.log`: If the directory in it
is not `/mnt/test-ext4/`, please change the directories to `/mnt/test-ext4`.
Also if you want to run the replayer on other file systems, you will need to
modify `init()` function in the code.

Use `make replayer` to build the replayer. Usage:

```
./replayer [prob_ckpt] [prob_restore]
```

`prob_ckpt` and `prob_restore` are integers representing the percentage number
of the probability of checkpointing and restoring respectively. They should be
in range of 0 and 50.

The replayer will output a line of message reporting sequence number, name of
the operation and arguments every time it performs an operation. It will stop
when encountering the bugs. Therefore the line count of the output can reflect
how early the bug manifested --- The fewer the line count is, the earlier the
bug is triggered.

### Auto replayer script

The script `./autoreplay.sh` will automatically replay the sequence of file
system operations in `sequence.log` using varied probability of checkpointing
and restoring. For each combination of the two probabilities, the script will
repeat the replayer 10 times, collect the line counts of the outputs and report
in CSV format.

