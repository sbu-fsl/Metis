#!/bin/bash

checkpoint() {
    # get the list of open nodes on which nfs-ganesha server is running.
    sudo lsof +E -aUc ganesha | grep STREAM | awk '{ print $8 }'

    sudo criu dump --tree `pgrep ganesha.nfsd` --images-dir $1 --external unix[1853539] --ext-unix-sk
}

restore() {
    sudo criu restore --images-dir $1 &
}

start_nfs_server() {
    set -x
    pushd .
    if pgrep -x ganesha.nfsd > /dev/null
    then
        kill -9 `pgrep ganesha.nfsd`
    fi
    cd ../../nfs-ganesha
    mkdir -p build
    cd build
    cmake -DUSE_FSAL_VFS=ON ../src
    make && make install
    ganesha.nfsd
    popd
}

stop_nfs_server() {
    kill -9 `pgrep ganesha.nfsd`
}