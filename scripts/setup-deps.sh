#!/bin/bash

#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

BASEDIR=$HOME
MCFS_BUILD_TYPE=Debug
OVERRIDES=()
CWD=$(pwd)
verbose=0

colorecho() {
    color=$1
    shift
    rest=$@
    $CWD/color.py "@$color\$$rest@!$";
}

should_override() {
    name=$1
    for overrided_item in ${OVERRIDES[@]}; do
        if [ "$name" = "$overrided_item" ] || [ "all" = "$overrided_item" ]; then
            return 0;
        fi
    done
    return 1;
}

runcmd() {
    if [ "$verbose" != "0" ]; then
        echo ">>> $@" >&2 ;
    fi
    sleep 0.5;
    $@;
    ret=$?;
    if [ $ret -ne 0 ]; then
        colorecho red "Command '$0' exited with error ($ret)." >&2;
        exit $ret;
    fi
}

install_pkg() {
    for pkg in $@;
    do
        colorecho cyan "Trying to install $pkg...";
        # Skip if the package has been installed
        if sudo dpkg -V "$pkg" 2>/dev/null; then
            if should_override $pkg; then
                colorecho green "Package $pkg has been installed, but user asked to override.";
                sudo dpkg -r $pkg;
            else
                colorecho green "Package $pkg has been installed, skip.";
                continue;
            fi
        fi
        # Report error if the package does not exist
        if ! apt-cache show "$pkg" 2>/dev/null >/dev/null; then
            colorecho red "Package $pkg does not exist in the software source!";
            return 1;
        fi
        sudo apt-get install -y $pkg;
        res=$?;
        if [ $res -ne 0 ]; then
            colorecho red "Failed to install $pkg. res is $res";
            return $res;
        fi
    done
}

check_repo() {
    name=$1
    if ! [ -d "$BASEDIR/$name" ]; then
        return 1;
    fi

    pushd $BASEDIR/$name;
    if git status -s 2>/dev/null >/dev/null; then
        popd;
        return 0;
    else
        popd;
        return 1;
    fi
}

prepare_repo() {
    name=$1
    repourl=$2
    if check_repo $name; then
        if should_override $name; then
            colorecho green "$name is already there, but user asked to override.";
            mv "$BASEDIR/$name" "$BASEDIR/$name.old";
        else
            colorecho green "$name is already there.";
	    return;
        fi
    fi
    if ! [ -d "$BASEDIR/$name" ]; then
        runcmd git clone --recurse-submodules $repourl;
    fi
    if [ -d "$BASEDIR/$name.old" ]; then
        rm -rf "$BASEDIR/$name.old"
    fi
}

# Parse command line options
while [[ $# -gt 0 ]]; do
    key=$1;
    case $key in
        -b|--basedir)
            BASEDIR=$2
            shift
            shift
            ;;
        -b=*|--basedir=*)
            BASEDIR=$(echo "$1" | cut -d '=' -f 2)
            shift
            ;;
        -t|--build-type)
            MCFS_BUILD_TYPE=$2
            shift
            shift
            ;;
        -t=*|--build-type=*)
            MCFS_BUILD_TYPE=$(echo "$1" | cut -d '=' -f 2)
            shift
            ;;
        -o|--override)
            OVERRIDES+=("$2")
            shift
            shift
            ;;
        -o=*|--override=*)
            value=$(echo "$1" | cut -d '=' -f 2)
            OVERRIDES+=("$value")
            shift
            ;;
        --invoke)
            shift
            func=$1;
	    colorecho cyan "Invoking function $func...";
            shift
            args=$@
	    colorecho cyan "Args is $args";
            $func $args
            exit;
            ;;
        *)
            colorecho red "Unrecognized parameter: $1"
            exit 1
            ;;
    esac
done

if [ "$MCFS_BUILD_TYPE" != "Debug" ] && [ "$MCFS_BUILD_TYPE" != "Release" ]; then
    colorecho red "Build type can only be either \"Debug\" or \"Release\", but supplied $MCFS_BUILD_TYPE.";
    exit 1;
fi

echo "Basedir = $BASEDIR";
echo "Build type = $MCFS_BUILD_TYPE";
echo -n "Overrided items:";
for item in ${OVERRIDES[@]}; do
    echo -n "$item ";
done
echo "";

install_nfs_ganesha() {
    pushd $BASEDIR;
    runcmd prepare_repo nfs-ganesha git@github.com:nfs-ganesha/nfs-ganesha.git;

    pwd;
    cd nfs-ganesha/src;
    mkdir -p build;
    cd build;
    if should_override nfs-ganesha; then
        rm -rf *;
    fi
    runcmd cmake -DCMAKE_BUILD_TYPE=$MCFS_BUILD_TYPE -DUSE_FSAL_CEPH=OFF -DUSE_FSAL_PROXY=OFF -DUSE_FSAL_GPFS=OFF -DUSE_FSAL_LUSTRE=OFF -DUSE_FSAL_GLUSTER=OFF -DUSE_9P=OFF -DUSE_ADMIN_TOOLS=OFF -DUSE_LTTNG=OFF -DUSE_FSAL_RGW=OFF -DUSE_9P_RDMA=OFF -D_USE_9P_RDMA=OFF -DUSE_NFS_RDMA=OFF -DUSE_GTEST=OFF -DUSE_RADOS_RECOV=OFF -DRADOS_URLS=OFF -DSANITIZE_ADDRESS=ON ..
    runcmd make -j $(nproc --all);
    runcmd sudo make install;
    popd;
}

install_xxHash() {
    pushd $BASEDIR;
    runcmd prepare_repo xxHash git@github.com:Cyan4973/xxHash.git;

    cd xxHash
    runcmd git checkout v0.8.0
    if should_override xxHash; then
        make clean;
    fi
    runcmd make;
    runcmd sudo make install;
    popd;
}

install_zlib() {
    pushd $BASEDIR;
    runcmd prepare_repo zlib git@github.com:madler/zlib.git;

    cd zlib
    runcmd git checkout master
    if should_override zlib; then
        make distclean;
    fi
    runcmd ./configure;
    runcmd make;
    runcmd sudo make install;
    popd;
}

install_verifs2() {
    pushd $BASEDIR;
    runcmd prepare_repo RefFS git@github.com:sbu-fsl/RefFS.git;

    cd RefFS
    if should_override RefFS; then
        rm -rf build;
    fi
    mkdir -p build;
    cd build;
    runcmd cmake ..;
    runcmd make;
    runcmd sudo make install;
    mkdir -p mnts;
    popd;
}

install_spin() {
    pushd $BASEDIR;
    runcmd prepare_repo fsl-spin git@github.com:sbu-fsl/fsl-spin.git;

    cd fsl-spin
    runcmd git checkout c-track-hooks;
    if should_override fsl-spin; then
        make clean;
    fi
    runcmd make;
    runcmd sudo make install;
    popd;
}

# This should be run without sudo
install_swarm() {
    pushd $BASEDIR;
    runcmd prepare_repo swarm-mcfs git@github.com:sbu-fsl/swarm-mcfs.git;

    cd swarm-mcfs
    runcmd git fetch
    runcmd git checkout swarm-v2;
    if should_override swarm-mcfs; then
        make clean;
    fi
    runcmd make;
    runcmd sudo cp Src/swarm /usr/local/bin/;
    popd;
}

colorecho cyan "Installing required packages..."
runcmd sudo apt update
# Basic tools and compilers
runcmd install_pkg gcc g++ git vim
runcmd install_pkg build-essential m4 autoconf bison flex cmake make
# Dependencies for MCFS
runcmd install_pkg mtd-tools libssl-dev
runcmd install_pkg libfuse-dev
runcmd install_pkg google-perftools
runcmd install_pkg libgoogle-perftools-dev
# Dependencies for nfs-ganesha
# Omitted on Ubuntu 22.04
# runcmd install_pkg libnfsidmap2
runcmd install_pkg libnfsidmap-dev
runcmd install_pkg libkrb5-3
runcmd install_pkg libkrb5-dev
runcmd install_pkg libk5crypto3
runcmd install_pkg libgssapi-krb5-2
runcmd install_pkg libgssglue1
runcmd install_pkg libdbus-1-3
runcmd install_pkg libattr1-dev
runcmd install_pkg libacl1-dev
runcmd install_pkg dbus
runcmd install_pkg libdbus-1-dev
runcmd install_pkg libcap-dev
runcmd install_pkg libjemalloc-dev
runcmd install_pkg uuid-dev
runcmd install_pkg libblkid-dev
runcmd install_pkg xfslibs-dev
runcmd install_pkg libwbclient-dev
#runcmd install_pkg pyqt4-dev-tools
runcmd install_pkg rpm2cpio
runcmd install_pkg libaio-dev
runcmd install_pkg libibverbs-dev
runcmd install_pkg librdmacm-dev
runcmd install_pkg rpcbind
runcmd install_pkg nfs-common
runcmd install_pkg libboost-all-dev
runcmd install_pkg liburcu-dev
runcmd install_pkg libxxhash-dev
runcmd install_pkg nilfs-tools

required_repos=(swarm spin zlib xxHash)

for repo in ${required_repos[@]}; do
    runcmd install_$repo;
done

colorecho green "Environment setup complete!";
