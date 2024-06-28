#!/bin/bash

NFS_VERIFS2_SZKB=0

cd ..
sudo ./stop.sh

sudo ./setup.sh -f nfs-verifs2:$NFS_VERIFS2_SZKB
