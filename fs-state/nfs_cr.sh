#!/bin/bash

checkpoint() {
    # get the list of open nodes on which nfs-ganesha server is running.
    local PORT=`sudo lsof +E -aUc ganesha | grep STREAM | awk '{ print $8 }' | head -n 1`

    sudo criu dump --tree `pgrep ganesha.nfsd` --images-dir $1 --external unix[$PORT] --ext-unix-sk
}

restore() {
    sudo criu restore --images-dir $1 &
}

start_nfs_server() {
    ganesha.nfsd
}

stop_nfs_server() {
    kill -9 `pgrep ganesha.nfsd`
}