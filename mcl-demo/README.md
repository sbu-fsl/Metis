# eXplode-MCL demo

This is a prototype file system checker written based on MCL (the model checker provided in eXplode codebase)

# Usage

1. Make sure you have [eXplode](https://github.com/sbu-fsl/explode-0.1pre) codebase on your computer and have built it;
2. Make sure RAM block device is enabled in your system (Check if `/dev/ram0` exists). If not, please use `sudo modprobe brd rd_size=1024` to enable the ramdisk device;
3. In Makefile, change `EXPLODE_PATH` to the path to eXplode codebase;
4. `make`
5. `sudo ./example`
