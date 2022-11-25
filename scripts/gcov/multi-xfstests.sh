#!/bin/bash

BTRFS_GROUPS=(quick generic all)

# Ext4 all
./xfstests_coverage.sh -f ext4 -g all

# BtrFS all generic quick
for name in ${BTRFS_GROUPS[@]}
do
	./xfstests_coverage.sh -f btrfs -g $name
done

echo "All ext4 and btrfs xfstests exps completed!"
