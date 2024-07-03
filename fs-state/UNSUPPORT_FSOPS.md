# Unsupported features and operations for file systems

While using MCFS, it is required to disable some operations (i.e., system calls) that are not supported by certain file systems under testing. Otherwise, one would return **ENOTSUP** error directly.

| VeriFS1                      | VeriFS2 | Ext2       | NOVA         | Kernel NFSv3 <br> (w/ VeriFS2) | Kernel NFSv4 <br>(w/ VeriFS2) |
| ---------------------------- | ------- | ---------- | ------------ | ------------------------------ | ----------------------------- |
| xattrs                       |         | fallocate  | setxattr     | xttars                         | xttars                        |
| rename                       |         |            | removexattr  |                                |                               |
| link & symlink & readlink    |         |            |              |                                |                               |
| mknod                        |         |            |              |                                |                               |
