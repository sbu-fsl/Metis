# `brd` - RAM block device driver

This is the modified `brd` linux kernel module that creates block devices backed
by system RAM (aka. Ramdisk). The original version of `brd` driver applies one
size to all devices it creates, which limits its flexibility and does not
satisfy our needs.

The issue is that different file systems may require different minimum sizes.
For example, ext4, ext2 and jffs2 can utilize small disks as little as 256KB,
whereas xfs requires 16MB and btrfs requires 110MB.  When testing the file
systems, we always want to use ramdisks that are as small as possible, because
we want to allow the model checker to explore more number of states with the
same amount of memory, and we would like to have the file systems reach corner
cases more quickly. Therefore, it's not a good idea to set `rd_size` to the
maximum of minimum size requirements among all file systems to be tested.

Therefore, I modified the source code of `brd` driver and here it is. This
modified version allows specifying individual size for each ramdisk it creates.

This kernel module is based on the original `brd` driver in linux 5.4. Therefore
it is strongly recommended that you use Ubuntu 20.04 when trying to compile and
load this module.

## Building the kernel module

```bash
make -C /lib/module/$(uname -r)/build M=$(pwd)
```

## Usage

```bash
sudo insmod brd.ko rd_nr=N, rd_sizes=size1,size2,size3,...,sizeN
```

- This command will create N ramdisks at `/dev/ram0`, `/dev/ram1`, `/dev/ram2`,
    ..., `/dev/ram{N-1}`, and the sizes are `size1`, `size2`, ..., `sizeN`
    respectively.

- If there are fewer sizes than the number of devices to be created (i.e. when
    `rd_nr=N, rd_sizes=size1,size2,...,sizeM` and N is greater than M), the
    (M+1)th to Nth ramdisks will have the size of `sizeM`.

- Currently `rd_sizes` can accept up to 32 sizes.

