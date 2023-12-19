#!/bin/bash

TERMTIME="40m"

CURRENT_DIR=$(pwd)
IOCOV_MCFS_DIR="../../IOCov/MCFS"

########### Figure 4: Input coverage for write sizes (40 mins) ###########

cd ../driver-fs-state

########### Metis-Uniform
CURRENT_PATTERN="write-size-Metis-Uniform"
./cleanup-iocov.sh
make clean

make MY_WRITE_SIZE_PATTERN=0

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

# Check if the script is still running and kill it if necessary
echo "[$CURRENT_PATTERN]: Time limit reached. Terminating the Metis."
# kill $SCRIPT_PID
# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

rm sequence-pan-*.log

PLOTNAME=""
for file in input-cov-mcfs-*.pkl; do
    PLOTNAME=$(echo "$file" | cut -d '-' -f 3- | sed 's/\..*$//')
    cp "$file" "../src/unfilter-$file"
    mv "$file" "../src/"
done

cd ../src/

python3 iocov-main.py $PLOTNAME --no-parse --plot -i

mv mcfs*_input_coords.pkl ../MCFS/

# back to ../../IOCov/MCFS folder
cd -

INPUT_COORDS_FILE=""

for file in mcfs*_input_coords.pkl; do
    INPUT_COORDS_FILE=$file
done

# Plot the figure
python3 plot-mcfs-input-write-sizes-40mins.py $CURRENT_PATTERN-$TERMTIME $INPUT_COORDS_FILE

echo "Completed plotting for $CURRENT_PATTERN-$TERMTIME, check ./IOCov/MCFS folder"

cp *.pdf $CURRENT_DIR

cd $CURRENT_DIR

########### Metis-XD, current in driver_scripts
# pwd: driver_scripts

CURRENT_PATTERN="write-size-Metis-XD"
./cleanup-iocov.sh
make clean

make MY_WRITE_SIZE_PATTERN=1

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

# Check if the script is still running and kill it if necessary
echo "[$CURRENT_PATTERN]: Time limit reached. Terminating the Metis."
# kill $SCRIPT_PID
# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

rm sequence-pan-*.log

PLOTNAME=""
for file in input-cov-mcfs-*.pkl; do
    PLOTNAME=$(echo "$file" | cut -d '-' -f 3- | sed 's/\..*$//')
    cp "$file" "../src/unfilter-$file"
    mv "$file" "../src/"
done

cd ../src/

python3 iocov-main.py $PLOTNAME --no-parse --plot -i

mv mcfs*_input_coords.pkl ../MCFS/

# back to ../../IOCov/MCFS folder
cd -

INPUT_COORDS_FILE=""

for file in mcfs*_input_coords.pkl; do
    INPUT_COORDS_FILE=$file
done

# Plot the figure
python3 plot-mcfs-input-write-sizes-40mins.py $CURRENT_PATTERN-$TERMTIME $INPUT_COORDS_FILE

echo "Completed plotting for $CURRENT_PATTERN-$TERMTIME, check ./IOCov/MCFS folder"

cp *.pdf $CURRENT_DIR

cd $CURRENT_DIR

########### Metis-IXD, current in driver_scripts
# pwd: driver_scripts

CURRENT_PATTERN="write-size-Metis-IXD"
./cleanup-iocov.sh
make clean

make MY_WRITE_SIZE_PATTERN=2

cd driver_scripts
./only_one_ext4.sh & 

# Wait for 40 minutes
sleep $TERMTIME

# Check if the script is still running and kill it if necessary
echo "[$CURRENT_PATTERN]: Time limit reached. Terminating the Metis."
# kill $SCRIPT_PID
# Back to driver_scripts folder
cd ..

./stop.sh

# pwd: driver_scripts

cp sequence-pan-*.log $IOCOV_MCFS_DIR

cd $IOCOV_MCFS_DIR

python3 parser-mcfs-log-input.py `ls sequence-pan-*.log`

rm sequence-pan-*.log

PLOTNAME=""
for file in input-cov-mcfs-*.pkl; do
    PLOTNAME=$(echo "$file" | cut -d '-' -f 3- | sed 's/\..*$//')
    cp "$file" "../src/unfilter-$file"
    mv "$file" "../src/"
done

cd ../src/

python3 iocov-main.py $PLOTNAME --no-parse --plot -i

mv mcfs*_input_coords.pkl ../MCFS/

# back to ../../IOCov/MCFS folder
cd -

INPUT_COORDS_FILE=""

for file in mcfs*_input_coords.pkl; do
    INPUT_COORDS_FILE=$file
done

# Plot the figure
python3 plot-mcfs-input-write-sizes-40mins.py $CURRENT_PATTERN-$TERMTIME $INPUT_COORDS_FILE

echo "Completed plotting for $CURRENT_PATTERN-$TERMTIME, check ./IOCov/MCFS folder"

cp *.pdf $CURRENT_DIR

cd $CURRENT_DIR

###########
echo "Figure 4: Input coverage for write sizes (40 mins) done."
