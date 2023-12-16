#!/bin/bash

########### Figure 3: Input coverage for open flags (40 mins) ###########
IOCOV_MCFS_DIR="../../IOCov/MCFS"

cd ../driver-fs-state

########### Metis-Uniform
make clean

make MY_OPEN_FLAG_PATTERN=0

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep 1m

# Check if the script is still running and kill it if necessary
echo "[Metis-Uniform open flags]: Time limit reached. Terminating the Metis."
# kill $SCRIPT_PID
# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

########### Metis-RSD, current in driver_scripts
# pwd: driver_scripts




########### Metis-IRSD


