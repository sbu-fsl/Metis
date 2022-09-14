# ext4 parameters
EXT4_SIZE=256 # in KiB for ramdisk
EXT4_MNT_DIR="/mnt/test-ext4"
EXT4_DEVICE="/dev/ram0"

setup_ext4() {
    modprobe brd rd_nr=1 rd_size=$EXT4_SIZE

    if test -n "$(mount | grep $EXT4_MNT_DIR)" ; then
        umount $EXT4_MNT_DIR || exit $?
    fi

    if test -d $EXT4_MNT_DIR ; then
        rm -rf $EXT4_MNT_DIR
    fi
    mkdir -p $EXT4_MNT_DIR

    mkfs.ext4 $EXT4_DEVICE
}

setup_ext4
./syscall_seqs $EXT4_MNT_DIR $EXT4_DEVICE ext4
