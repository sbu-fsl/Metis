#!/bin/bash

########### Figure 4: Input coverage for write sizes (40 mins) ###########
IOCOV_MCFS_DIR="../../IOCov/MCFS"
TERMTIME="1m"

cd ../driver-fs-state

########### Metis-Uniform
make clean

make MY_WRITE_SIZE_PATTERN=0

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

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

rm sequence-pan-*.log

cd -
########### Metis-XD, current in driver_scripts
# pwd: driver_scripts

make clean

make MY_WRITE_SIZE_PATTERN=1

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

# Check if the script is still running and kill it if necessary
echo "[Metis-RSD open flags]: Time limit reached. Terminating the Metis."

# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

rm sequence-pan-*.log

cd -
########### Metis-IXD

make clean

make MY_WRITE_SIZE_PATTERN=2

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

# Check if the script is still running and kill it if necessary
echo "[Metis-IRSD open flags]: Time limit reached. Terminating the Metis."

# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

rm sequence-pan-*.log

cd -

echo "Figure 4: Input coverage for write sizes (40 mins) done."
