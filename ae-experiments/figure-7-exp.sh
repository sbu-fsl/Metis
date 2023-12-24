#!/bin/bash

FS_STATE_DIR="../fs-state"
SCRIPT_DIR="../fs-state/mcfs_scripts"
TIMERUN="30m"
CURRENT_DIR=$(pwd)
RESULTFILE="fig7_fs_perf_results"

########### Figure 7: Performance comparison between RefFS and other file systems with Metis ###########
rm $RESULTFILE

##### RefFS performance with Metis
CURRENT_FS="RefFS"
cd $FS_STATE_DIR
make clean

cd $SCRIPT_DIR
./only_one_fs.sh verifs2 $TIMERUN

### pwd: fs-state/mcfs_scripts
# Change to fs-state folder
cd .. 

### pwd: fs-state
# Analyze perf-pan*.csv and get performance values
PERFCSV=$(ls perf-pan*.csv)

rm ${CURRENT_FS}_results

tail -n 1 $PERFCSV | awk -F, '{print $1, $2, $3}' | {
    read NSECONDS NOPS NSTATES

    # Now NSECONDS, NOPS, and NSTATES are treated as strings
    # You can use them in calculations with tools like bc
    # For example:
    ops_per_second=$(echo "$NOPS / $NSECONDS" | bc -l)
    states_per_second=$(echo "$NSTATES / $NSECONDS" | bc -l)

    echo "$CURRENT_FS Operations per second: $ops_per_second" >> $RESULTFILE
    echo "$CURRENT_FS States per second: $states_per_second" >> $RESULTFILE
}

echo "$CURRENT_FS run finished, check $RESULTFILE file."

cd $CURRENT_DIR

##### XFS performance with Metis
CURRENT_FS="XFS"
cd $FS_STATE_DIR
make clean

cd $SCRIPT_DIR
./only_one_fs.sh xfs $TIMERUN

### pwd: fs-state/mcfs_scripts
# Change to fs-state folder
cd .. 

### pwd: fs-state
# Analyze perf-pan*.csv and get performance values
PERFCSV=$(ls perf-pan*.csv)

rm ${CURRENT_FS}_results

tail -n 1 $PERFCSV | awk -F, '{print $1, $2, $3}' | {
    read NSECONDS NOPS NSTATES

    # Now NSECONDS, NOPS, and NSTATES are treated as strings
    # You can use them in calculations with tools like bc
    # For example:
    ops_per_second=$(echo "$NOPS / $NSECONDS" | bc -l)
    states_per_second=$(echo "$NSTATES / $NSECONDS" | bc -l)

    echo "$CURRENT_FS Operations per second: $ops_per_second" >> $RESULTFILE
    echo "$CURRENT_FS States per second: $states_per_second" >> $RESULTFILE
}

echo "$CURRENT_FS run finished, check $RESULTFILE file."

cd $CURRENT_DIR

##### BtrFS performance with Metis
CURRENT_FS="BtrFS"
cd $FS_STATE_DIR
make clean

cd $SCRIPT_DIR
./only_one_fs.sh btrfs $TIMERUN

### pwd: fs-state/mcfs_scripts
# Change to fs-state folder
cd .. 

### pwd: fs-state
# Analyze perf-pan*.csv and get performance values
PERFCSV=$(ls perf-pan*.csv)

rm ${CURRENT_FS}_results

tail -n 1 $PERFCSV | awk -F, '{print $1, $2, $3}' | {
    read NSECONDS NOPS NSTATES

    # Now NSECONDS, NOPS, and NSTATES are treated as strings
    # You can use them in calculations with tools like bc
    # For example:
    ops_per_second=$(echo "$NOPS / $NSECONDS" | bc -l)
    states_per_second=$(echo "$NSTATES / $NSECONDS" | bc -l)

    echo "$CURRENT_FS Operations per second: $ops_per_second" >> $RESULTFILE
    echo "$CURRENT_FS States per second: $states_per_second" >> $RESULTFILE
}

echo "$CURRENT_FS run finished, check $RESULTFILE file."

cd $CURRENT_DIR

##### Ext4 performance with Metis
CURRENT_FS="Ext4"
cd $FS_STATE_DIR
make clean

cd $SCRIPT_DIR
./only_one_fs.sh ext4 $TIMERUN

### pwd: fs-state/mcfs_scripts
# Change to fs-state folder
cd .. 

### pwd: fs-state
# Analyze perf-pan*.csv and get performance values
PERFCSV=$(ls perf-pan*.csv)

rm ${CURRENT_FS}_results

tail -n 1 $PERFCSV | awk -F, '{print $1, $2, $3}' | {
    read NSECONDS NOPS NSTATES

    # Now NSECONDS, NOPS, and NSTATES are treated as strings
    # You can use them in calculations with tools like bc
    # For example:
    ops_per_second=$(echo "$NOPS / $NSECONDS" | bc -l)
    states_per_second=$(echo "$NSTATES / $NSECONDS" | bc -l)

    echo "$CURRENT_FS Operations per second: $ops_per_second" >> $RESULTFILE
    echo "$CURRENT_FS States per second: $states_per_second" >> $RESULTFILE
}

echo "$CURRENT_FS run finished, check $RESULTFILE file."

cd $CURRENT_DIR

##### Ext2 performance with Metis
CURRENT_FS="Ext2"
cd $FS_STATE_DIR
make clean

cd $SCRIPT_DIR
./only_one_fs.sh ext2 $TIMERUN

### pwd: fs-state/mcfs_scripts
# Change to fs-state folder
cd .. 

### pwd: fs-state
# Analyze perf-pan*.csv and get performance values
PERFCSV=$(ls perf-pan*.csv)

rm ${CURRENT_FS}_results

tail -n 1 $PERFCSV | awk -F, '{print $1, $2, $3}' | {
    read NSECONDS NOPS NSTATES

    # Now NSECONDS, NOPS, and NSTATES are treated as strings
    # You can use them in calculations with tools like bc
    # For example:
    ops_per_second=$(echo "$NOPS / $NSECONDS" | bc -l)
    states_per_second=$(echo "$NSTATES / $NSECONDS" | bc -l)

    echo "$CURRENT_FS Operations per second: $ops_per_second" >> $RESULTFILE
    echo "$CURRENT_FS States per second: $states_per_second" >> $RESULTFILE
}

echo "$CURRENT_FS run finished, check $RESULTFILE file."

cd $CURRENT_DIR

##### Check all results_perf_* files about file system performance with Metis
cat results_perf_*

exit 0
