# JFS Kernel Crash Bug Reproduction

We have prepared scripts to reproduce a non-deterministic Kernel Crash bug (likely a race) in the Journaled File System (JFS). We have used Linux Kernel v6.6.1 and v6.9.4 in our experiments, however, we recommend using v6.9.4. A sample dmesg kernel log, captured while this crash was triggered using our replayer on JFS (mounted on a ramdisk with Linux v6.9.4), is available in this repository as dmesg_jfs_kernel_oops_trace.txt.

### Setting up the Environment
We need to install Linux Kernel v6.9.4 before using the replayer. We have provided a kernel config, .kernel-6.9.4-config, that corresponds to the kernel used by us during the above experiment. On a Linux machine, follow the below steps to setup a Kernel with v6.9.4.

(**Note: Backup/Snapshot your machine before installing a new Kernel, as this operation can often leave your machine in an inconsistent state.**)

* First clone the respository using the following git command:
> git clone https://github.com/sbu-fsl/Metis-Replayer.git

This will clone the repo in a folder name Metis-Replayer

* In order to compile the kernel you will need to install some packages, for Debian/Ubuntu Linux (the distro used for our experiments) use the below command for installation:
> sudo apt-get install build-essential libncurses-dev bison flex libssl-dev libelf-dev

* Then clone the Kernel source code, extract it and then cd into the folder:
> wget https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.9.4.tar.xz

> tar -xf linux-6.9.4.tar.xz

> cd linux-6.9.4

* Post this, copy the provided kernel config to the Linux kernel source directory and name it .config (the command assumes that Metis-Replayer has been cloned in the root folder):
> cp ~/Metis-Replayer/.kernel-6.9.4-config .config

* Use the configuration tool to ensure your .config file is correctly set up.
> make oldconfig

* Compile the kernel
> make -j$(nproc)

* Compile kernel modules
> sudo make modules_install

* Install the compiled kernel
> sudo make install

After executing the above steps reboot your machine and run the below command to verify that you have successfully installed Linux Kernel v6.9.4:
> uname -mars

### Setting up JFS
Once you have installed the kernel, you can proceed ahead to setup the ramdisk for JFS. First we have to ensure that the ramdisk device (/dev/ram0 in our case) is available, and if so delete it and set it up from scratch. We do so using the following commands:
> sudo umount /dev/ram0

> sudo rm /dev/ram*

> sudo rmmod brd

* Now to setup JFS, execute the following command:

> sudo bash ./setup_jfs.sh

Depending upon the function invoked (setup_jfs_on_ramdev or setup_jfs_on_loopdev) in the script, this command sets up up a ramdisk (/dev/ram0 of size 16 MiB) or a loop device, initializes it using dd, and finally sets up the JFS file system.  Note that we are using all the default options while setting up JFS.

### Running the Replayer
* Then compile the replayer using the following command:

> make replayer

This will produce an executable named 'replay'

* Post this execute the below command:

> sudo bash ./loop_replay.sh

This command replays the sequence of all operations (823,178 in total) captured in the jfs_op_sequence.log file, in a loop for a total of 500 iterations.  Due to the bug's non-deterministic nature, we have found that replaying the log in a loop for 500 iterations results in a high probability of reproducing the bug within a day. In our experiments, we encountered the bug after about 60-300 iterations. Correspondingly, the time taken to trigger the bug ranged from about 9 to 75 hours (on our VM).

### Cleaning up the Resources
Before performing further experiments, make sure that the ramdisk has been safely deleted, using the same commands as mentioned previously:

> sudo umount /dev/ram0

> sudo rm /dev/ram*

> sudo rmmod brd
