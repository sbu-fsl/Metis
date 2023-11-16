#!/bin/bash

MNTPNT="/mnt/test-nilfs2"
IMGFILE="./nilfs2-dev-88-unmount-hanging.img"
FTRACE_DIR="/sys/kernel/debug/tracing"

# Recompile NILFS2 kernel module
./recompile_nilfs2_mod.sh

# Mount an existing image to create a NILFS2 filesystem
./mount_nilfs2_img.sh $MNTPNT $IMGFILE

# Create an already-existing file to reproduce the unmount hanging bug
cd $MNTPNT/d-00
touch f-02
cd -

echo "Start Unmounting..."
##### Enable ftrace tracing
cd $FTRACE_DIR

# Set up Function Filters
# All nilfs2 functions and down_write/up_write functions
sudo bash -c 'echo nilfs_* > set_ftrace_filter'
sudo bash -c 'echo down_write >> set_ftrace_filter'
sudo bash -c 'echo up_write >> set_ftrace_filter'

# Enable function tracer
sudo bash -c 'echo function > current_tracer'

# Tracing specific PID
sudo bash -c 'echo $$ > set_ftrace_pid'

# Targetted tracing (trace events related to a specific command)
sudo bash -c 'echo 1 > tracing_on'

# Clear the trace
sudo sh -c 'echo 0 > trace'

# Unmounting to reproduce hanging
umount $MNTPNT

# Disable ftrace tracing
sudo bash -c 'echo 0 > tracing_on'
sudo bash -c 'echo nop > current_tracer'

echo "Reproducer finished (not supposed to see this message due to hanging)."
