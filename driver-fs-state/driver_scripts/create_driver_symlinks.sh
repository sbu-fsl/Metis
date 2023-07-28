#!/bin/bash

# This script should be placed in driver-fs-state/driver_scripts folder
# Create symbolic links for all required driver files from fs-state folder

# Files not required by the driver: 
# Markdown: *.md (except README.md)
# Replayer: replay*.c replay*.h autoreplay.sh min_repro.c min_repro_driver.sh
# Others:   whichconfig.h 

# FILES REQUIRED BY THE DRIVER
# config.h fileutil.{c,h} init_globals.{c,h} load*.sh mcfs-main.pml
# mount.c perf.c set.{cpp,h} setup.{c,h} setup*.sh stop.sh swarm.lib*

# FILES SHOULD BE UNIQUE FOR DRIVER 
# Makefile parameters.py parameter_util.py



