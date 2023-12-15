#!/bin/bash

#
# Copyright (c) 2020-2023 Yifei Liu
# Copyright (c) 2020-2023 Wei Su
# Copyright (c) 2020-2023 Erez Zadok
# Copyright (c) 2020-2023 Stony Brook University
# Copyright (c) 2020-2023 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

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
