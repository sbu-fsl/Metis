#!/bin/bash

cd ~/Metis/fs-state/mcfs_scripts

# num blocks
for p in 60; do
for b in 16; do 
    # num bytes
    for d in 1028; do
        # device size
        for n in "1MiB"; do
            # # nsegments_per_clean
            for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 -s $s -f 5 -p $p > ~/Metis/fs-state/experiment_results/07-12_run_d${n}_b${b}_ram_min2max4_p${p}_s${s}_1.log 2>&1; done;

            # for x in 4 8 16; do for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 --nseg $x -s $s -f 10 > ~/Metis/fs-state/experiment_results/06-28_run_d${n}_b${b}_ram_10_min2max4_nSegPerClean${x}_s${s}.log 2>&1; done; done;
            # for x in 8 16; do for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 --mc_nseg $x -s $s -f 10 > ~/Metis/fs-state/experiment_results/06-28_run_d${n}_b${b}_ram_10_min2max4_mcNSegPerClean${x}_s${s}.log 2>&1; done; done;

   done
    done
done
done
# for b in 16; do 
#     # num bytes
#     for d in 2052; do
#         # device size
#         for n in "2MiB"; do
#             # # nsegments_per_clean
#             for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 -s $s -f 20 > ~/Metis/fs-state/experiment_results/06-28_run_d${n}_b${b}_ram_20_min2max4_default_s${s}.log 2>&1; done;

#             # for x in 4 8 16; do for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 --nseg $x -s $s -f 10 > ~/Metis/fs-state/experiment_results/06-28_run_d${n}_b${b}_ram_10_min2max4_nSegPerClean${x}_s${s}.log 2>&1; done; done;
#             # for x in 8 16; do for s in 20; do ./experiment.sh -m -d $d -b $b --min 2 --max 4 --mc_nseg $x -s $s -f 10 > ~/Metis/fs-state/experiment_results/06-28_run_d${n}_b${b}_ram_10_min2max4_mcNSegPerClean${x}_s${s}.log 2>&1; done; done;

#    done
#     done
# done