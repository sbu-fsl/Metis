# fs-state - filesystem state testing

## Usage

### Prerequisites

> [SPIN](http://spinroot.com/spin/whatispin.html)

### Using shell script

To test using shell script, simply run:

```bash
sudo sh ./setup.sh
```

### Using Makefile

If you want to use Makefile to run this filesystem state test, please make sure you have created imgfile or device and mounted a filesystem on it. Make necessary changes to `demo.pml` if there uses different mount point and f/s image name. After the tested filesystem is set up, run:

```bash
make
make run
```

Use `make clean` to clean resources, i.e., the SPIN generated files (pan*), test dirs and files.

## Design

### `setup.sh`

Basically the `setup.sh` script creates a loop device and mounts filesystem on it, and then use `demo.pml` to test f/s syscalls. The steps performed by this script are as follows:

1. Use `dd` to create a virtual disk image file.
2. Use `losetup -D` to detach all the associated loop devices.
3. Use `losetup` to find the first unused loop device and set up loop device with the image file.
4. Create file system on loop device.
5. Create mount point and mount filesystem on mount point.
6. Compile the test program by `make`.
7. Run test program and write the program output to output.log.
8. Cleanup.

### `demo.pml`

`demo.pml` conducts a full-state space search to the f/s operations and sets checkpoint (`fsimg_checkpoint` in `fileutil.c`) to every f/s syscall that can synchronize the updates of fsimg memory and get the MD5 hash of the fsimg to track if there has changes for f/s image file.

`demo.pml` runs selected f/s syscalls, including open, write, close, unlink, mkdir, rmdir, on the mount point (with specific f/s). The logic of this program is to run these syscalls in Promela's atomic block and find the full statespace of them. `demo.pml` supports testing multiple filesystems and images; for each syscall, it will run `assert` to verify if these multiple filesystems have the same behaviors (no discrepancy).

To capture every executed syscall, `demo.pml` prints the time cost, function name, arguments, return value of each syscall as well as the MD5 hash of f/s image file.
