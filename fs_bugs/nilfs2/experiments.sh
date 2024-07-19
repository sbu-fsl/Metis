#!/bin/bash

cd ~/Metis/fs-state/mcfs_scripts

# num blocks
for b in ; do 
    # num bytes
    for d in 65540; do
        # device size
        for n in "1024MiB"; do
            for s in 0; do ./single_experiment.sh -m -d $d -b $b -s $s > ~/Metis/fs-state/experiment_results/run_d${n}_b${b}_ram_default_s${s}.log 2>&1; done;

            # max_clean_segments
            for x in "50%" "75%" "100%"; do for s in 0; do ./single_experiment.sh -m -d $d -b $b --max $x -s $s > ~/Metis/fs-state/experiment_results/run_d${n}_b${b}_ram_maxCleanSeg${x}_s${s}.log 2>&1; done; done;

            # # nsegments_per_clean
            for x in 8 16; do for s in 0; do ./single_experiment.sh -m -d $d -b $b --nseg $x -s $s > ~/Metis/fs-state/experiment_results/run_d${n}_b${b}_ram_nSegPerClean${x}_s${s}.log 2>&1; done; done;

            # mc_nsegments_per_clean
            for x in 8; do for s in 0; do ./single_experiment.sh -m -d $d -b $b --mc_nseg $x -s $s > ~/Metis/fs-state/experiment_results/run_d${n}_b${b}_ram_mcNSegPerClean${x}_s${s}.log 2>&1; done; done;
        done
    done
done
# cleaning_interval
# for x in 1 10; do for s in 0 15; do ./single_experiment.sh -m --cl_intvl $x -s $s > ~/Metis/fs-state/experiment_results/run_d1028KiB_b16_ram_cleanIntvl${x}_s${s}.log 2>&1; done; done

# retry_interval
# for x in 10; do for s in 0 15; do ./single_experiment.sh -m --retry $x -s $s > ~/Metis/fs-state/experiment_results/run_d1028KiB_b16_ram_retry${x}_s${s}.log 2>&1; done; done

# min_reclaimable_blocks
# for x in "0%" "5%" "20%" "50%"; do for s in 0 15; do ./single_experiment.sh -m --min_reclaim $x -s $s > ~/Metis/fs-state/experiment_results/run_d1028KiB_b16_ram_minReclaim${x}_s${s}.log 2>&1; done; done

# mc_min_reclaimable_blocks
# for x in "0%" "5%"; do for s in 0 15; do ./single_experiment.sh -m --mc_min_reclaim $x -s $s > ~/Metis/fs-state/experiment_results/run_d1028KiB_b16_ram_mcMinReclaim${x}_s${s}.log 2>&1; done; done
