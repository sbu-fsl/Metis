#!/bin/bash

NFS_GANESHA_VERIFS2_SZKB=0

cd ..
sudo ./stop.sh

# sudo ./setup.sh -f nfs-ganesha-verifs2:$NFS_GANESHA_VERIFS2_SZKB:verifs2:$NFS_GANESHA_VERIFS2_SZKB
sudo ./setup.sh -f nfs-ganesha-verifs2:$NFS_GANESHA_VERIFS2_SZKB
