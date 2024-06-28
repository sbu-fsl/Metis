#!/bin/bash

NFS_VERIFS2_SZKB=0
VERIFS2_SZKB=0

cd ..
sudo ./stop.sh

sudo ./setup.sh -f nfs-verifs2:$NFS_VERIFS2_SZKB:verifs2:$VERIFS2_SZKB
