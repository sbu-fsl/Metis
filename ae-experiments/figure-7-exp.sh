#!/bin/bash

FS_STATE_DIR="../fs-state"
SCRIPT_DIR="../fs-state/mcfs_scripts"
TIMERUN="2m"

########### Figure 7: Performance comparison between RefFS and other file systems with Metis ###########

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

    echo "Operations per second: $ops_per_second" >> results_perf_${CURRENT_FS}
    echo "States per second: $states_per_second" >> results_perf_${CURRENT_FS}
}

echo "$CURRENT_FS run finished, check results_perf_${CURRENT_FS} file."

##### Ext4 performance with Metis


##### Ext2 performance with Metis



##### XFS performance with Metis


##### BtrFS performance with Metis
