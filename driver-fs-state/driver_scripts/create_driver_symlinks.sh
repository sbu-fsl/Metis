#!/bin/bash

# This script should be placed in driver-fs-state/driver_scripts folder
# Create symbolic links for all required driver files from fs-state folder

# Files not required by the driver: 
# Markdown: *.md (except README.md)
# Replayer: replay*.c replay*.h autoreplay.sh min_repro.c min_repro_driver.sh
# Others:   whichconfig.h 

# FILES REQUIRED BY THE DRIVER
# config.h fileutil.c fileutil.h init_globals.c init_globals.h loadlargebrds.sh loadmods.sh 
# mount.c parameter_util.py perf.c set.cpp set.h setup.c setup.h setup.sh setup_swarm.sh stop.sh swarm.lib swarm.lib.copy

# FILES SHOULD BE UNIQUE FOR DRIVER 
# Makefile parameters.py mcfs-main.pml (because we use different operations for driver)

SYMLK_FILES="config.h fileutil.c fileutil.h init_globals.c init_globals.h loadlargebrds.sh loadmods.sh mount.c parameter_util.py perf.c set.cpp set.h setup.c setup.h setup.sh setup_swarm.sh stop.sh swarm.lib swarm.lib.copy"

cd ../../fs-state

FILES_ARR=( $(ls $SYMLK_FILES) )

cd ../driver-fs-state
# For each checker file, create a symbolic link in driver-fs-state/driver_scripts
for CFILE in "${FILES_ARR[@]}"; do
    ln -s ../fs-state/$CFILE $CFILE
done

echo "Symlinks created from checker (fs-state) to driver (driver-fs-state)"

