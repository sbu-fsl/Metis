#!/bin/bash

checkpoint() {
    # get the list of open nodes on which nfs-ganesha server is running.
    local PORT=`lsof +E -aUc ganesha | grep STREAM | awk '{ print $8 }' | head -n 2 | tail -n 1`
    mkdir -p nfs_imgs/$1
    criu dump --tree `pgrep ganesha.nfsd` --shell-job --images-dir nfs_imgs/$1 --external unix[$PORT] --ext-unix-sk --leave-running --track-mem
}

restore() {
    criu restore --shell-job --images-dir nfs_imgs/$1 --ext-unix-sk &
}

if [ $1 == "c" ]; then
    checkpoint $2
else
    restore $2
fi