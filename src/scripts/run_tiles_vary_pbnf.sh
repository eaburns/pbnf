#!/bin/bash

for min in 32
do
    for (( threads=1; threads <= 8; threads++ ))
    do
        ./scripts/run_tiles.sh pbnf -m $min -t $threads $@
    done
done
