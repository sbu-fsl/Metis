# JFS Kernel Hang Bug Reproduction

We have prepared scripts to reproduce the Kernel Hang bug in JFS.

* To setup JFS, execute the following command:

> sudo bash ./setup_jfs.sh

This command setups up a ramdisk of size 16 MiB, formats it using dd, creates a mountpoint and finally mounts the JFS filesystem. Note that we are using all the default options while setting up JFS.

* Then compile the replayer using the following command:

> make replayer

This will produce an executable named 'replay'

* Post this execute the below command:

> sudo bash ./loop_replay.sh

This command replays the sequence of operations capture in the jfs_op_sequence.log file, in a loop for a total of 100 times. A single execution of the replayer takes around 4 minutes. Through our experiments we have found that this approach helps us in reproducing the non-deterministic kernel hang bug for more than 50% of the executions. 
