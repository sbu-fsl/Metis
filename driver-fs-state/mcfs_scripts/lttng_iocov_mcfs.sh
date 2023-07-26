#!/bin/bash

# Run this script with sudo

# Make sure the ramdisk has been rmmod'd
# Set MCFS runtime limit as 1 hour 
# It's 1 hour, ext4 256KB dev with 1 VT

FS=ext4
DEVSZ=256 # in KiB
TIMELIMIT=1h

MCFS_FOLDER="/mcfs2/LTTng-xfstests-2022-1211/nfs4mc/fs-state"

SYSCALLS=("open" "openat" "creat" "read" "pread64" "write" "pwrite64" "lseek" "llseek" "truncate" "ftruncate" "mkdir" "mkdirat" "chmod" "fchmod" "fchmodat" "close" "close_range" "chdir" "fchdir")

SUFFIX="mcfs-"
SCPARAM=""

for sc in ${SYSCALLS[@]}; do
    SCPARAM="${SCPARAM}${sc},"
done

SUFFIX="${SUFFIX}${FS}-${DEVSZ}"
# discard the last comma
SCPARAM="${SCPARAM::-1}"

# mcfs-ext4-256
# echo "SUFFIX: $SUFFIX"
# open,openat,creat,read,pread64,write,pwrite64,lseek,llseek,truncate,ftruncate,mkdir,mkdirat,chmod,fchmod,fchmodat,close,close_range,chdir,fchdir
# echo "SCPARAM: $SCPARAM"

cd $MCFS_FOLDER
./loadmods.sh

# lttng create my-kernel-session-mcfs-ext4-256 --output=/tmp/my-kernel-trace-mcfs-ext4-256
lttng create my-kernel-session-${SUFFIX} --output=/tmp/my-kernel-trace-${SUFFIX}

# lttng enable-event --kernel --syscall open,openat,creat,read,pread64,write,pwrite64,lseek,llseek,truncate,ftruncate,mkdir,mkdirat,chmod,fchmod,fchmodat,close,close_range,chdir,fchdir
lttng enable-event --kernel --syscall $SCPARAM

start=`date +%s`
lttng start

timeout $TIMELIMIT ./setup.sh -f ${FS}:${DEVSZ}

# lttng stop
lttng stop

# lttng destroy
lttng destroy

# chown -R $(whoami) /tmp/my-kernel-trace-mcfs-ext4-256
chown -R $(whoami) /tmp/my-kernel-trace-${SUFFIX}

cd -

end=`date +%s`
runtime=$((end-start))

# babeltrace2 /tmp/my-kernel-trace-mcfs-ext4-256/kernel > mcfs-lttng-mcfs-ext4-256-chdir-fchdir.log
babeltrace2 /tmp/my-kernel-trace-mcfs-ext4-256/kernel > mcfs-lttng-mcfs-ext4-256-chdir-fchdir-${TIMELIMIT}-${runtime}.log
