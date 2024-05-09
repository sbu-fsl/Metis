#!/bin/bash

NFS_GANESHA_VERIFS2_SZKB=256

cd ..
sudo ./stop.sh

sudo ./setup.sh -f nfs-ganesha-verifs2:$NFS_GANESHA_VERIFS2_SZKB
