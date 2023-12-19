#!/bin/bash

DRIVER_FS_STATE_DIR="../driver-fs-state"
IOCOV_MCFS_DIR="../../IOCov/MCFS"
IOCOV_SRC_DIR="../../IOCov/src"
DEMO_FIGS_DIR="../../IOCov/src/Assets/Input-Figures"

rm $DRIVER_FS_STATE_DIR/*.log $DRIVER_FS_STATE_DIR/*.csv $DRIVER_FS_STATE_DIR/*.txt 
rm $IOCOV_MCFS_DIR/*.json $IOCOV_MCFS_DIR/*.pkl $IOCOV_MCFS_DIR/*.log
rm $IOCOV_SRC_DIR/*.json $IOCOV_SRC_DIR/*.pkl $IOCOV_SRC_DIR/*.log
rm $DEMO_FIGS_DIR/*.pdf
