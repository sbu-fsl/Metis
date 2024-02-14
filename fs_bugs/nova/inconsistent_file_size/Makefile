#File:   Makefile
#Date:   February 9, 2024
#Brief:  This compiles driver.c and runs it

# Copyright (c) 2020-2024 Gautam Ahuja
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache
# License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).

#Usage: 
#	make (compiles driver)
#	sudo make run-driver (compiles driver, prepares mountpoint, and runs the driver)
#	make clean (removes compiled files)

CC=gcc
override CFLAGS += -g

#Configurable parameters:

#Maximum number of times to run the mount-unmount tight loop
DRIVER_LOOP_MAX=10000000

#Mountpoint for nova
NOVA_MNT_DIR="/mnt/novatest"

#The pmem device which the fs is mounted on
PMEM_DEVICE="/dev/pmem0"

driver: driver.c
	$(CC) -o driver driver.c  $(CFLAGS)

unmount:
	if test -n "$$(mount | grep $(PMEM_DEVICE))" ; then \
		umount $(PMEM_DEVICE) || exit $$? ; \
	fi ;

remove-directory:
	rm -rf $(NOVA_MNT_DIR)

create-directory:
	mkdir -p $(NOVA_MNT_DIR)

add-module:
	modprobe nova

run-driver: unmount remove-directory create-directory add-module driver
	./driver $(NOVA_MNT_DIR) $(PMEM_DEVICE) $(DRIVER_LOOP_MAX)

clean:
	rm -f *.o driver
