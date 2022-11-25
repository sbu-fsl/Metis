#!/bin/bash

SERVER=sgdp05
FSCHECKER=xfstests

FSTYPE=ext4
GROUP=generic

# Parse command line options
# -f filesystem-to-test  -g group name (all, quick, generic)
while [[ $# -gt 0 ]]; do
    key=$1;
    case $key in
        -f|--fs)
            FSTYPE="$2"
            shift
            shift
            ;;
        -g|--group)
            GROUP="$2"
            shift
            shift
            ;;
        *)
            POSITIONAL+=("$1")
            shift
            ;;
    esac
done

KERNEL_EXT4_SRC="/sys/kernel/debug/gcov/mcfs/Linux_Kernel_Install/linux-6.0.6/fs/$FSTYPE"

SUFFIX="${FSTYPE}_${GROUP}"

CURDIR=$PWD
OUTPUT_INFO="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_coverage_${SUFFIX}.info"
OUTPUT_DIR="$CURDIR/gcov_results/${SERVER}_${FSCHECKER}_cov_out_${SUFFIX}"

XFSTESTS_DIR="/mcfs/gcov_test_2022_1029/fsl-xfstests"
XFSTESTS_RUNNER="run_fsl_xfstests.sh"

cd $XFSTESTS_DIR

sudo lcov --zerocounters

start=`date +%s`
./$XFSTESTS_RUNNER -f $FSTYPE -g $GROUP
end=`date +%s`
runtime=$((end-start))

lcov --capture --directory $KERNEL_EXT4_SRC --rc lcov_branch_coverage=1 --output-file $OUTPUT_INFO
genhtml $OUTPUT_INFO --rc genhtml_branch_coverage=1 --output-directory ${OUTPUT_DIR}_${runtime}

cd -
echo "Total Tests Runtime: " $runtime
