#!/bin/bash

probs=(1 2 5 10 20 30 40 50)
round=10

for p_ckpt in ${probs[@]}; do
    for p_rest in ${probs[@]}; do
        echo -n "$p_ckpt,$p_rest,";
        for i in $(seq $round); do
            nlines=$(./replay $p_ckpt $p_probs 2>&1 | wc -l)
            echo -n "$nlines,";
        done
        echo "";
    done
done
