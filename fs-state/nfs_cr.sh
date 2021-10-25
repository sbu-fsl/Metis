#!/bin/bash

checkpoint() {
    # get the list of open nodes on which nfs-ganesha server is running.
    local PORT=`lsof +E -aUc ganesha | grep STREAM | awk '{ print $8 }' | head -n 1`

    criu dump --tree `pgrep ganesha.nfsd` --images-dir $1 --external unix[$PORT] --ext-unix-sk
}

restore() {
    criu restore --images-dir $1 &
}

start_nfs_server() {
    ganesha.nfsd
}

stop_nfs_server() {
    kill -9 `pgrep ganesha.nfsd`
}

if [ $1 == "c" ]; then
    checkpoint $2
else
    restore $2
fi