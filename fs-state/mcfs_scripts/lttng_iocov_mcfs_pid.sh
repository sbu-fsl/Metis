#!/bin/bash

# Run this script with sudo

# Make sure the ramdisk has been rmmod'd
# Set MCFS runtime limit as 1 hour 
# It's 1 hour, ext4 256KB dev with 1 VT

# PROCESS: LTTng tracks system calls from a single process (MCFS pan) only [make sure MCFS enables sleep to get pid]
# ALL: LTTng tracks system calls from all kernel event
TRACE_OPTION="PROCESS"

FS=ext4
DEVSZ=256 # in KiB
TIMELIMIT=10m

MCFS_FOLDER="/mcfs2/LTTng-xfstests-2022-1211/nfs4mc/fs-state"

SYSCALLS=("open" "openat" "creat" "read" "pread64" "write" "pwrite64" "lseek" "llseek" "truncate" "ftruncate" "mkdir" "mkdirat" "chmod" "fchmod" "fchmodat" "close" "close_range" "chdir" "fchdir" "setxattr" "lsetxattr" "fsetxattr" "getxattr" "lgetxattr" "fgetxattr")

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

if [ "$TRACE_OPTION" = "PROCESS" ]; then
    timeout $TIMELIMIT ./setup.sh -f ${FS}:${DEVSZ} &
fi

# lttng create my-kernel-session-mcfs-ext4-256 --output=/tmp/my-kernel-trace-mcfs-ext4-256
lttng create my-kernel-session-${SUFFIX} --output=/tmp/my-kernel-trace-${SUFFIX}

# lttng enable-event --kernel --syscall open,openat,creat,read,pread64,write,pwrite64,lseek,llseek,truncate,ftruncate,mkdir,mkdirat,chmod,fchmod,fchmodat,close,close_range,chdir,fchdir,setxattr,lsetxattr,fsetxattr,getxattr,lgetxattr,fgetxattr
if [ "$TRACE_OPTION" = "PROCESS" ]; then
    lttng enable-event --kernel --syscall $SCPARAM --pid=$(pgrep pan)
elif [ "$TRACE_OPTION" = "ALL" ]; then
    lttng enable-event --kernel --syscall $SCPARAM
else
    echo "Trace option $TRACE_OPTION is not supported.  Exit."
    exit 1
fi

start=`date +%s`
lttng start

if [ "$TRACE_OPTION" = "PROCESS" ]; then
    sleep $TIMELIMIT
elif [ "$TRACE_OPTION" = "ALL" ]; then
    timeout $TIMELIMIT ./setup.sh -f ${FS}:${DEVSZ}
fi

# lttng stop
lttng stop

# lttng destroy
lttng destroy

# chown -R $(whoami) /tmp/my-kernel-trace-mcfs-ext4-256
chown -R $(whoami) /tmp/my-kernel-trace-${SUFFIX}

cd -

end=`date +%s`
runtime=$((end-start))

# babeltrace2 /tmp/my-kernel-trace-mcfs-ext4-256/kernel > mcfs-lttng-mcfs-ext4-256-xattr.log
babeltrace2 /tmp/my-kernel-trace-mcfs-ext4-256/kernel > mcfs-lttng-mcfs-ext4-256-xattr-${TRACE_OPTION}-${TIMELIMIT}-${runtime}.log
