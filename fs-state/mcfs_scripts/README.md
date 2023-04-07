# Usage of MCFS to Test Various File Systems

## Minimum device size for different file systems

BtrFS: 16 MiB, must use mkfs.btrfs -M option
F2FS: 38 MiB
XFS: 16 MiB
NILFS2: 1028 KiB, with minimum segments with -B option: 16
JFS: 16 MiB

## Run single-VT MCFS for each file systems
First of all, we need to make sure the devices with desired size are available.

Ext4 vs. Ext2:
```bash
./setup.sh -f ext4:256:ext2:256
```

Ext4 vs. JFFS2:
```bash
./setup.sh -f ext4:256:jffs2:256
```

Ext4 vs. NILFS2:
```bash
./setup.sh -f ext4:256:nilfs2:1028
```

Ext4 vs. XFS:
```bash
./setup.sh -f ext4:256:xfs:16384
```

Ext4 vs. BtrFS:
```bash
./setup.sh -f ext4:256:btrfs:16384
```

Ext4 vs. F2FS:
```bash
./setup.sh -f ext4:256:f2fs:38912
```

Ext4 vs. JFS:
```bash
./setup.sh -f ext4:256:jfs:16384
```
