#!/bin/bash

# This script should be placed in fs-state/mcfs_scripts folder

cd ..
sudo ./stop.sh

sudo ./setup.sh -f verifs2:0
