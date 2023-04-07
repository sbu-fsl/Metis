# VeriFS1 (or CRMFS, Checkpoint-Restore in-Memory File System)

## Known VeriFS1 Bugs:

### VeriFS1 cannot create a file [Fixed 2023-04-06]

This bug appeared while enabled `-DFILEDIR_POOL` and `-DCOMPLEX_FSOPS`. The
`create_file` operation for VeriFS1 succeeded with return 0 and no error 
number, but the file does not exist after the `create_file` operation.

This bug can be reproduced by MCFS either VeriFS1 vs. VeriFS2 or Ext4 vs.
VeriFS1.
